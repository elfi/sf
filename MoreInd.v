Require Export Logic.

Check nat_ind.

Theorem mult_0_r': forall n : nat,
    n * 0 = 0.
Proof.
    apply nat_ind.
    Case "O". reflexivity.
    Case "S". simpl. intros n H. apply H.
Qed.

Theorem plus_one_r': forall n : nat,
    n + 1 = S n.
Proof.
    apply nat_ind.
    Case "O". simpl. reflexivity.
    Case "S". simpl. intros n H. apply eq_remove_S. apply H.
Qed.

Inductive yesno: Type :=
| yes : yesno
| no : yesno.

Check yesno_ind.

(* rgb_ind: 
   forall P : rgb -> Prop,
     P red ->
     P green ->
     P blue ->
     forall y : rgb, P y *)

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

Check rgb_ind.

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.

(* natlist_ind :
   forall P : natlist -> Prop,
     P nnil ->
     (forall n : nat, forall l : natlist, P l -> P (ncons y l)) ->
     forall n : natlist, P n *)

Check natlist_ind.

Inductive natlist1 : Type :=
| nnil1 : natlist1
| nsnoc1 : natlist1 -> nat -> natlist1.

(* natlist1_ind:
   forall P : natlist1 -> Prop,
     P nnil1 ->
     (forall l : natlist1, P l -> forall n : nat, P (nsnoc1 l n)) ->
     forall n : natlist1, P n *)

Check natlist1_ind.

(* False_ind:
   forall P : Prop, False -> P *)

Check False_ind.

Inductive byntree : Type :=
| bempty : byntree
| bleaf : yesno -> byntree
| nbranch : yesno -> byntree -> byntree -> byntree.

(* byntree_ind :
   forall P : byntree -> Prop,
     P bempty ->
     (forall y : yesno, P (bleaf y)) ->
     (forall y : yesno, forall b1 : byntree, P b1 -> 
        (forall b2 : byntree, P b2 -> P (nbranch y b1 b2))) ->
     forall n : byntree, P n *)

Check byntree_ind.

Inductive ExSet : Type :=
| con1 : bool -> ExSet
| con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

Inductive tree (X:Type) : Type :=
| leaf : X -> tree  X
| node : tree X -> tree X -> tree X.

(* tree_ind:
   forall (X:Type) (P : tree -> Prop),
     (forall (x:X), P (leaf X x)) ->
     (forall (l1:list X), P l1 -> (forall (l2:list X), P l2 ->
        P (node X l1 l2))) ->
     forall l:tree, P l *)

Check tree_ind.

Inductive mytype (X:Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

Inductive foo (X Y : Type) : Type :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

Inductive foo' (X:Type) : Type :=
| C1 : list X -> foo' X -> foo' X
| C2 : foo' X.

(* foo'_ind:
   forall (X : Type) (P : foo' X -> Prop),
     (forall (l : list X) (f : foo' X),
         P f ->
         P (C1 X l f)) ->
     P (C2 X) ->
   forall f : foo' X, P f *)

Check foo'_ind.
