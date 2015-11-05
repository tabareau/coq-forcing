Declare ML Module "forcing".

Require Import Omega. 
(* Axiom Obj : Type. *)
(* Axiom Hom : Obj -> Obj -> Type. *)

Definition Obj := nat.
Definition Hom : Obj -> Obj -> Type := fun n m => n <= m.

Notation "P ≤ Q" := (forall R, Hom R Q -> Hom R P) (at level 70).
Notation "#" := (fun (R : Obj) (k : Hom R _) => k).
Notation "g ∘ f" := (fun (R : Obj) (k : Hom R _) => g R (f R k)) (at level 40).

Ltac _force c := force Obj Hom c.

Goal True.
Proof.
  _force (Type -> Type).
  assert (Later : forall n, (fun (p p0 : Obj) (_ : p ≤ p0) =>
       (forall p1 : Obj,
        p0 ≤ p1 ->
        (fun (p2 : Obj) (_ : p1 ≤ p2) => forall p3 : Obj, p2 ≤ p3 -> Type)
          p1 #) ->
       (fun (p1 : Obj) (_ : p0 ≤ p1) => forall p2 : Obj, p1 ≤ p2 -> Type)
         p0 #) n n #).
  {intros n f m e. destruct m.
  - exact unit.
  - assert (n ≤ m).
    { clear -e. intros k h. apply (e k). unfold Hom in *. omega. }
    exact (f n # m X).
  }
_force (fun (A : Type) (x : A) => x).
_force (fun (A : Type) (P : forall x : A, Type) (x : A) => P x).
_force (forall A : Type, (A -> Type) -> A -> Type).
_force (fun (A : Type) (x : A) (y : A) => forall (P : A -> Type), P x -> P y).
_force (forall A : Type, A -> A -> Type).
_force ((fun (A : Type) (x : A) => x) Type (forall A : Type, A -> A)).
_force (fun (A B : Type) (x : A) (y : B) => forall (P : A -> B -> Type) (Q : B -> Type), P x y -> Q y).

Abort.
