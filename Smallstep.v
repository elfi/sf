Require Export Imp.

Inductive tm: Type :=
| C : nat -> tm         (* Constant *)
| P : tm -> tm -> tm.   (* Plus *)

Tactic Notation "tm_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "C" | Case_aux c "P" ].

(* big-step style *)

Fixpoint evalF (t : tm) : nat :=
    match t with
    | C n => n
    | P a1 a2 => evalF a1 + evalF a2
    end.

Reserved Notation " t '|| n " (at level 50, left associativity).

Inductive eval : tm -> nat -> Prop :=
| E_Const : forall n,
        C n || n
| E_Plus : forall t1 t2 n1 n2,
        t1 || n1 ->
        t2 || n2 ->
        P t1 t2 || (n1 + n2)

where " t '||' n " := (eval t n).

Tactic Notation "eval_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "E_Const" | Case_aux c "E_Plus" ].

Module SimpleArith1.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* the only reduction step *)
| ST_PlusConstConst : forall n1 n2,
        P (C n1) (C n2) ==> C (n1 + n2)
  (* expand on t1, eventually reaching state
     where the first or third rule apply *)
| ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
  (* t1 now must be a constant, expand on t2,
     eventually reaching state where
     the first or second rule apply *)
| ST_Plus2: forall n1 t2 t2',
        t2 ==> t2' ->
        P (C n1) t2 ==> P (C n1) t2'

where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ST_PlusConstConts"
    | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

Example test_step_1 :
    P (P (C 0) (C 3))
      (P (C 2) (C 4))
    ==>
    P (C (0 + 3))
      (P (C 2) (C 4)).
Proof.
    apply ST_Plus1. apply ST_PlusConstConst.
Qed.

Example test_step_2 :
    P (C 0)
      (P (C 2)
         (P (C 0) (C 3)))
    ==>
    P (C 0)
      (P (C 2)
         (C (0 + 3))).
Proof.
    apply ST_Plus2. apply ST_Plus2. apply ST_PlusConstConst.
Qed.






