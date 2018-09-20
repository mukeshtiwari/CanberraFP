Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.


Module Type Monad.
  Parameter m : Type -> Type.

  (* return *)
  Parameter ret : forall (A : Type), A -> m A.

  (* bind *)
  Parameter bind : forall (A B : Type), m A -> (A -> m B) -> m B.

  (* Remove this  so that unfolding is intutitive 
  Infix ">>=" := bind (at level 50, left associativity). *)

  Axiom left_id : forall (A B : Type) (x : A) (f : A -> m B),
    bind A B (ret A x) f = f x.


  Axiom right_id : forall (A : Type) (x : m A),
    bind A A x (ret A) = x.

 
  Axiom bind_assoc :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      bind B C (bind A B n f) g = bind A C n (fun x => bind _ _ (f x) g).

End Monad.
  



Module Option <: Monad.
  Definition m := option.

  Definition ret (A : Type) := @Some A.

  Definition bind (A B : Type) (n : m A) (f : A -> m B) : m B :=
    match n with
    | None => None
    | Some x => f x
    end.

  
  Theorem left_id : forall (A B : Type) (x : A) (f : A -> m B),
      bind A B (ret A x) f = f x.
  Proof.
    unfold bind, ret.
    refine (fun A B x f => eq_refl).
  Qed.
  
  
  Theorem right_id : forall (A : Type) (x : m A),
      bind A A x (ret A) = x.
  Proof.
    unfold bind, ret.
    refine (fun A x =>
                match x with
                | Some y => eq_refl
                | _ => eq_refl
                end).
  Qed.
  
  (* Coq can infer types if we leave _ *)
  Theorem bind_assoc :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      bind B C (bind A B n f) g = bind _ _ n (fun x => bind _ _ (f x) g).
  Proof.
    unfold bind. 
    refine (fun A B C n f g =>
              match n with
              | Some _ => eq_refl
              | None => eq_refl
              end).
  Qed.
  

  (* https://en.wikipedia.org/wiki/Monad_(functional_programming)#fmap_and_join *)
  Definition fmap (A B : Type) (f : A -> B) (n : m A) : m B :=
    bind A B n (compose (ret B) f).
  
 
  Definition join (A : Type) (n : m (m A)) : m A :=
    bind (m A) A n id.

  Theorem fmap_compose_join_eq_bind :
    forall (A B : Type) (n : m A) (f : A -> m B),
      bind A B n f = join B (fmap A (m B) f n).
  Proof.
    unfold join, fmap, bind, compose, ret, id.
    refine (fun A B n f =>
              match n with
              | Some x => eq_refl
              | None => eq_refl
              end).
  Qed.
  
  
  Theorem fmap_id :
    forall (A : Type), fmap A _ id = id .
  Proof.
    unfold fmap, bind, compose, ret, id.
    refine (fun A : Type =>
              functional_extensionality
                (fun n : m A => match n with
                             | Some x => Some x
                             | None => None
                             end) (fun x : m A => x)
                (fun x => match x with
                       | Some y => eq_refl
                       | None => eq_refl
                       end)).
  Qed.
  
 
  Theorem fmap_associativity :
    forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap _ _ (compose g f) = compose (fmap _ _ g) (fmap _ _ f).
  Proof.
    unfold fmap, bind, ret, compose, id.
    refine (fun A B C f g =>
              functional_extensionality _ _ _).
    
                
                

    
    intros. unfold fmap, compose, ret. 
    apply functional_extensionality.  intros.
    destruct x.  simpl. auto.
    simpl. auto.  
  Qed.
  
  Theorem return_property :
    forall (A B : Type) (f : A -> B) (x : A),
      ret (f x) = fmap f (ret x).
  Proof.
    unfold fmap. unfold compose. unfold ret. intros.
    rewrite left_id. auto.
  Qed. 

End Option. 
  


Module List <: Monad.
  Require Import Coq.Lists.List.
  Definition m := list. 

  Definition ret {A : Type} (x : A) := cons x nil.

  Definition bind {A B : Type} (n : list A) (f : A -> list B) :=
    concat (map f n).
   
 Infix ">>=" := bind (at level 50, left associativity).
  (* m is option *)
  Theorem left_id : forall (A B : Type) (x : A) (f : A -> m B),
      ret x >>= f = f x.
  Proof.
    intros. unfold ret. unfold bind.
    simpl. rewrite <- app_nil_end.
    auto. 
  Qed.  
  
  Theorem right_id : forall (A : Type) (x : m A),
      x >>= ret = x.
  Proof.
    intros. unfold ret.  unfold bind.
    induction x.
    simpl; auto.
    simpl. f_equal. auto.  
  Qed.
  
  Theorem bind_assoc :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      (n >>= f) >>= g = n >>= (fun x => f x >>= g).
  Proof.
    intros. unfold bind.  
    induction n.
    simpl.  auto.
    simpl. rewrite map_app.
    rewrite concat_app. f_equal. 
    auto.
  Qed.

  Definition fmap {A B : Type} (f : A -> B) (n : m A) : m B :=
    n >>= compose ret f.
  
  Definition join {A : Type} (n : m (m A)) : m A :=
    n >>= id.
  
  
  Theorem fmap_compose_join_eq_bind :
    forall (A B : Type) (n : m A) (f : A -> m B),
      n >>= f = join (fmap f n).
  Proof.
    unfold join. unfold fmap. unfold compose. 
    intros. rewrite bind_assoc.  
    f_equal. apply functional_extensionality.  intros.
    rewrite left_id. auto.
  Qed.

  
  
  Theorem fmap_id :
    forall (A : Type), fmap (@id A) = @id (m A).
  Proof.
    intros. unfold fmap. apply functional_extensionality.
    intros. unfold compose. rewrite right_id. auto.
  Qed.
  
  Theorem fmap_associativity :
    forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap (compose g f) = compose (fmap g) (fmap f).
  Proof.
    intros. unfold fmap, compose.
    apply functional_extensionality.  intros.
    rewrite bind_assoc.  f_equal.
  Qed.
  

  Theorem return_property :
    forall (A B : Type) (f : A -> B) (x : A),
      ret (f x) = fmap f (ret x).
  Proof.
    unfold fmap. unfold compose. intros.
    rewrite left_id. auto.
  Qed.

End List.




  