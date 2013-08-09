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
