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
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..).

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
    | x :: xs => S (length xs)
    end.

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | x :: xs => cons x (app xs l2)
    end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.

Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
    match l with
    | nil => default
    | x :: xs => x
    end.

Definition tail (l:natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => xs
    end.

Example test_hd1: hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tail: tail [1,2,3] = [2,3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | 0 :: tail => nonzeros tail
    | x :: tail => x :: nonzeros tail
    end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => match oddb x with
                 | true => x :: oddmembers xs
                 | false  => oddmembers xs
                 end
    end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
    match l with
    | nil => 0
    | x :: xs => match oddb x with
                 | true => S (countoddmembers xs)
                 | false => countoddmembers xs
                 end
    end.

Example countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.

Example countoddmembers2: countoddmembers [0,2,4] = 0.
Proof. reflexivity. Qed.

Example countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1,l2 with
    | nil, l2 => l2
    | l1, nil => l1
    | x :: xs, y :: ys => x :: y :: alternate xs ys
    end.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. reflexivity. Qed.

Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof. reflexivity. Qed.

Example test_alternate3: alternate [] [20,30] = [20,30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
    | nil => 0
    | x :: xs => match beq_nat x v with
                 | true => S (count v xs)
                 | false => count v xs
                 end
    end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
    app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
    v :: s.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1,4,1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
    match count v s with
    | 0 => false
    | S n' => true
    end.

Example test_member1: member 1 [1,4,1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1,4,1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) :=
    match s with
    | nil => nil
    | x :: xs => match beq_nat x v with
                 | true => xs
                 | false => x :: remove_one v xs
                 end
    end.

Example test_remone_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remone_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remone_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.

Example test_remone_one4: count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. reflexivity. Qed.


