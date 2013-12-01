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
    [ Case_aux c "ST_PlusConstConst"
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

Definition relation (X : Type) := X -> X -> Prop.

Definition deterministic {X : Type} (R : relation X) :=
    forall x y1 y2 : X,
    R x y1 -> R x y2 -> y1 = y2.

Theorem step_deterministic:
    deterministic step.
Proof.
    unfold deterministic. intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    step_cases (induction Hy1) Case; intros y2 Hy2.
    Case "ST_PlusConstConst".
        step_cases (inversion Hy2) SCase.
        SCase "ST_PlusConstConst".
            reflexivity.
        SCase "ST_Plus1".
            inversion H2.
        SCase "ST_Plus2".
            inversion H2.
    Case "ST_Plus1".
        step_cases (inversion Hy2) SCase.
        SCase "ST_PlusConstConst".
            rewrite <- H0 in Hy1. inversion Hy1.
        SCase "ST_Plus1".
            rewrite <- (IHHy1 t1'0). reflexivity. assumption.
        SCase "ST_Plus2".
            rewrite <- H in Hy1. inversion Hy1.
    Case "ST_Plus2".
        step_cases (inversion Hy2) SCase.
        SCase "ST_PlusConstConst".
            rewrite <- H1 in Hy1. inversion Hy1.
        SCase "ST_Plus1".
            inversion H2.
        SCase "ST_Plus2".
            rewrite <- (IHHy1 t2'0). reflexivity. assumption.
Qed.

End SimpleArith1.

Inductive value : tm -> Prop :=
    v_const : forall n, value (C n).


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
| ST_Plus2: forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        P v1 t2 ==> P v1 t2'

where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ST_PlusConstConst"
    | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

Theorem step_deterministic :
    deterministic step.
Proof.
    unfold deterministic. intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    step_cases (induction Hy1) Case; intros y2 Hy2.
    Case "ST_PlusConstConst".
        step_cases (inversion Hy2) SCase.
        SCase "ST_PlusConstConst".
            reflexivity.
        SCase "ST_Plus1".
            inversion H2. (* constant does not step *)
        SCase "ST_Plus2".
            inversion H3. (* constant does not step *)
    Case "ST_Plus1".
        step_cases (inversion Hy2) SCase.
        SCase "ST_PlusConstConst".
            (* constant does not step *)
            rewrite <- H0 in Hy1. inversion Hy1.
        SCase "ST_Plus1".
            rewrite <- (IHHy1 t1'0).
            reflexivity. assumption.
        SCase "ST_Plus2".
            (* value does not step *)
            inversion H1. rewrite <- H4 in Hy1. inversion Hy1.
    Case "ST_Plus2".
        step_cases (inversion Hy2) SCase.
        SCase "ST_PlusConstConst".
            rewrite <- H2 in Hy1. inversion Hy1.
        SCase "ST_Plus1".
            inversion H. rewrite <- H4 in H3. inversion H3.
        SCase "ST_Plus2".
            rewrite <- (IHHy1 t2'0).
            reflexivity. assumption.
Qed.

Theorem strong_progress: forall t,
    value t \/ (exists t', t ==> t').
Proof.
    tm_cases (induction t) Case.
    Case "C".
        left. apply v_const.
    Case "P".
        right. inversion IHt1.
        SCase "left part, value t1".
            inversion IHt2.
            SSCase "left part, value t2".
                inversion H. inversion H0.
                exists (C (n + n0)).
                apply ST_PlusConstConst.
            SSCase "right part, exists t', t2 ==> t'".
                inversion H0 as [t' H1].
                exists (P t1 t').
                apply ST_Plus2. apply H. apply H1.
        SCase "right part, exists t', t1 ==> t'".
            inversion H as [t' H0].
            exists (P t' t2).
            apply ST_Plus1. apply H0.
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
    ~ exists t', R t t'.

Lemma value_is_nf: forall v,
    value v -> normal_form step v.
Proof.
    unfold normal_form. intros v H. inversion H.
    intro contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value: forall t,
    normal_form step t -> value t.
Proof. (* a corollary of strong progres *)
    unfold normal_form. intros t H.
    assert (G: value t \/ exists t', t ==> t') by
        (apply strong_progress).
    inversion G as [left_part | right_part].
    Case "value".
        apply left_part.
    Case "contra".
        apply H in right_part. inversion right_part.
Qed.

Corollary nf_same_as_value: forall t,
    normal_form step t <-> value t.
Proof.
    split. apply nf_is_value. apply value_is_nf.
Qed.

Module Temp1.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n)
| v_funny : forall t1 n2, value (P t1 (C n2)).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
        P (C n1) (C n2) ==> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2
| ST_Plus2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        P v1 t2 ==> P v1 t2'

where " t '==>' t' " := (step t t').

Lemma value_not_same_as_normal_form:
    exists v, value v /\ ~ normal_form step v.
Proof.
    exists (P (C 1) (C 2)).
    split.
    Case "left".
        apply v_funny.
    Case "right".
        unfold normal_form. intro contra. apply contra.
        exists (C (1 + 2)). apply ST_PlusConstConst.
Qed.

End Temp1.



