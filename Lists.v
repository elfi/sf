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

Theorem snd_fst_is_swop : forall (p:natprod),
    (snd p, fst p) = swap_pair p.
Proof.
    intro p. destruct p as (m,n).
    simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p:natprod),
    fst (swap_pair p) = snd p.
Proof.
    intro p. destruct p as (m,n).
    simpl. reflexivity.
Qed.

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1,2,3].

Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => 0
    | x :: xs => S (lenght xs)
    end.




