Require Export Induction.

Module NatList.

Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p:natprod) : nat :=
    match p with
    | pair x y => x
    end.

Definition snd (p:natprod) : nat :=
    match p with
    | pair x y => y
    end.

Eval simpl in (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3,5)).

Definition swap_pair (p:natprod) : natprod :=
    match p with
    | (x,y) => (y,x)
    end.

Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)). (* structure exposed *)
Proof.
    reflexivity.
Qed.

Theorem surjective_pairing : forall (p:natprod),
    p = (fst p, snd p).
Proof.
    intro p. destruct p as (m,n). (* or destruct p as [m n] *)
    simpl. reflexivity.
Qed.


