Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

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
              functional_extensionality (fun x =>
                                             match x with
                                             | Some y => Some (g (f y))
                                             | None => None
                                             end) _ _). (* Now terms are getting messier *)
    intros.
    refine (match x with
            | Some y => _
            | None => _
            end); auto.
  Qed.
  
                
  Theorem return_property :
    forall (A B : Type) (f : A -> B) (x : A),
      ret _ (f x) = fmap _ _ f (ret _ x).
  Proof.
    unfold fmap, bind, ret, compose.
    refine (fun A B f x => eq_refl).
  Qed.
  
End Option. 
  
Module List <: Monad. 
  Definition m := list.
  
  Definition ret (A : Type) (x : A) := cons x nil.
  
  Definition bind (A B : Type) (n : m A) (f : A -> m B) :=
    concat (map f n).
   
  Theorem left_id : forall (A B : Type) (x : A) (f : A -> m B),
      bind _ _ (ret _ x) f = f x.
  Proof.
    unfold bind, ret.
    cbn. refine (fun A B x f =>
                   app_nil_r (f x)).
  Qed. 
  
  Theorem right_id : forall (A : Type) (x : m A),
      bind _ _ x (ret _) = x.
  Proof.
    unfold bind, ret.
    refine (fun A =>
              fix F x :=
              match x with
              | [] => eq_refl
              | h :: t => _
              end); cbn.
    specialize (F t). rewrite F.
    exact eq_refl.
  Qed.
  
  
  Theorem bind_assoc :
     forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
       bind B C (bind A B n f) g = bind _ _ n (fun x => bind _ _ (f x) g).
  Proof.
    unfold bind.
    refine (fun A B C =>
              fix F n :=
              match n with
              | [] => fun f g => eq_refl
              | h :: t => fun f g => _
              end); cbn.
    rewrite map_app, concat_app.
    specialize (F t f g); rewrite F.
    exact eq_refl.
  Qed.
  

  Definition fmap (A B : Type) (f : A -> B) (n : m A) : m B :=
    bind _ _ n (compose (ret _) f).
  
  Definition join (A : Type) (n : m (m A)) : m A :=
    bind _ _ n id.
  
  
  Theorem fmap_compose_join_eq_bind :
    forall (A B : Type) (n : m A) (f : A -> m B),
      bind _ _ n f = join _ (fmap _ _ f n).
  Proof.
    unfold join, fmap, compose.
    refine (fun A B n f => _);
      rewrite bind_assoc.
    f_equal. refine (functional_extensionality _ _ _).
    refine (fun x => _). rewrite left_id.
    exact eq_refl.
  Qed.
  
  
  Theorem fmap_id :
    forall (A : Type), fmap A _ id = id.
  Proof.
    unfold fmap, compose, id.
    refine (fun A => functional_extensionality _ _ _).
    refine (fun x => _); rewrite right_id.
    exact eq_refl.
  Qed.
  
  
  Theorem fmap_associativity :
    forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap _ _ (compose g f) = compose (fmap _ _ g) (fmap _ _ f).
  Proof.
    unfold fmap, compose.
    refine (fun A B C f g => functional_extensionality _ _ _).
    refine (fun x => _). rewrite bind_assoc.
    f_equal.
  Qed.
  

  Theorem return_property :
    forall (A B : Type) (f : A -> B) (x : A),
      ret _ (f x) = fmap _ _ f (ret _ x).
  Proof.
    unfold fmap, compose.
    refine (fun A B f x => _).
    rewrite left_id. exact eq_refl.
  Qed.

End List.

Module State <: Monad.

  (* M is the type of State *)
  Parameter M : Type. 

  Definition state (A : Type) :=  M -> prod A M.
  
  Definition m (A : Type) := state A.
  
  Definition ret (A : Type) (a : A) :=
    fun (s : M) => (a, s).
  

  Definition bind (A B : Type) (n : m A) (f : A -> m B) :=
     fun (s : M ) => let (r, s') := n s in f r s'.

  Theorem left_id : forall (A B : Type) (x : A) (f : A -> m B),
      bind  A _ (ret A x) f = f x.
  Proof.
    unfold bind, ret.
    refine (fun A B x f =>
              functional_extensionality _ _ (fun y => eq_refl)).
  Qed.

  Theorem right_id : forall (A : Type) (x : m A),
      bind _ _ x (ret _) = x.
  Proof.
    unfold bind, ret.
    refine (fun A x =>
              functional_extensionality _ _ (fun y => _)).
    destruct (x y); auto.
  Qed.

  Theorem bind_assoc :
     forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
       bind B C (bind A B n f) g = bind _ _ n (fun x => bind _ _ (f x) g).
  Proof.
    unfold bind.
    refine (fun A B C n f g =>
              functional_extensionality _ _ (fun y => _)).
    destruct (n y); exact eq_refl.
  Qed.

   Definition fmap (A B : Type) (f : A -> B) (n : m A) : m B :=
    bind _ _ n (compose (ret _) f).
  
  Definition join (A : Type) (n : m (m A)) : m A :=
    bind _ _ n id.

End State.

