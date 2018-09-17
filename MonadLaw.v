Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Basics.

Set Implicit Arguments.

Module Type Monad.
  Parameter m : Type -> Type.

  (* return *)
  Parameter ret : forall {A : Type}, A -> m A.

  (* bind *)
  Parameter bind : forall {A B : Type}, m A -> (A -> m B) -> m B.

  Infix ">>=" := bind (at level 50, left associativity).

  Axiom left_id : forall (A B : Type) (x : A) (f : A -> m B),
    ret x >>= f = f x.

  Axiom right_id : forall (A : Type) (x : m A),
    x >>= ret = x.

  Axiom bind_assoc :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      (n >>= f) >>= g = n >>= (fun x => f x >>= g).

  Definition fmap {A B : Type} (f : A -> B) (n : m A) : m B :=
    n >>= compose ret f.

  Definition join {A : Type} (n : m (m A)) : m A :=
    n >>= id.

  
  Theorem fmap_compose_join_eq_bind :
    forall (A B : Type) (n : m A) (f : A -> m B),
      n >>= f = join (fmap f n).
  Proof.
    unfold join. unfold fmap. unfold compose.  intros.
    rewrite bind_assoc.
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
    apply functional_extensionality. intros.
    rewrite left_id.  auto. 
  Qed.

  Theorem return_property :
    forall (A B : Type) (f : A -> B) (x : A),
      ret (f x) = fmap f (ret x).
  Proof.
    unfold fmap. unfold compose. intros.
    rewrite left_id. auto.
  Qed.

End Monad.


Module Option <: Monad.
  Definition m := option.

  Definition ret {A : Type} := @Some A.

  Definition bind {A B : Type} (n : m A) (f : A -> m B) : m B :=
    match n with
    | None => None
    | Some x => f x
    end.

  Infix ">>=" := bind (at level 50, left associativity).
  (* m is option *)
  Theorem left_id : forall (A B : Type) (x : A) (f : A -> m B),
      ret x >>= f = f x.
  Proof.
    (* firstorder *)
    intros. unfold ret. unfold bind.
    auto. 
  Qed.
  
  
  Theorem right_id : forall (A : Type) (x : m A),
      x >>= ret = x.
  Proof.
    intros. unfold ret.  unfold bind.
    destruct x; auto. 
  Qed.
  
  
  Theorem bind_assoc :
    forall (A B C : Type) (n : m A) (f : A -> m B) (g : B -> m C),
      (n >>= f) >>= g = n >>= (fun x => f x >>= g).
  Proof.
    intros. destruct n. simpl.  auto.
    simpl.  auto. 
  Qed.
  
  
  Definition fmap {A B : Type} (f : A -> B) (n : m A) : m B :=
    n >>= compose ret f.
  
  Definition join {A : Type} (n : m (m A)) : m A :=
    n >>= id.
  

  
  Theorem fmap_compose_join_eq_bind :
    forall (A B : Type) (n : m A) (f : A -> m B),
      n >>= f = join (fmap f n).
  Proof. 
    unfold join. unfold fmap. unfold compose.  intros.
    destruct n. simpl. auto. 
    simpl. auto. 
  Qed.
  
  
  Theorem fmap_id :
    forall (A : Type), fmap (@id A) = @id (m A).
  Proof.
    intros. unfold fmap. unfold compose. unfold ret. 
    apply functional_extensionality. intros.
    destruct x.  simpl. auto.
    simpl. auto.
  Qed.
  
  Theorem fmap_associativity :
    forall (A B C : Type) (f : A -> B) (g : B -> C),
      fmap (compose g f) = compose (fmap g) (fmap f).
  Proof.
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


  