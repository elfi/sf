Require Export Smallstep.

Hint Constructors multi.

Inductive tm : Type :=
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm
| tzero : tm
| tsucc : tm -> tm
| tpred : tm -> tm
| tiszero : tm -> tm.

Inductive bvalue : tm -> Prop :=
| bv_true : bvalue ttrue
| bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
| nv_zero : nvalue tzero
| nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.
Hint Unfold extend.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_IfTrue : forall t1 t2,
        (tif ttrue t1 t2) ==> t1
| ST_IfFalse : forall t1 t2,
        (tif tfalse t1 t2) ==> t2
| ST_If : forall t1 t1' t2 t3,
        t1 ==> t1' ->
        (tif t1 t2 t3) ==> (tif t1' t2 t3)
| ST_Succ : forall t1 t1',
        t1 ==> t1' ->
        (tsucc t1) ==> (tsucc t1')
| ST_PredZero :
        (tpred tzero) ==> tzero
| ST_PredSucc : forall t1,
        nvalue t1 ->
        (tpred (tsucc t1)) ==> t1
| ST_Pred : forall t1 t1',
        t1 ==> t1' ->
        (tpred t1) ==> (tpred t1')
| ST_IszeroZero :
        (tiszero tzero) ==> ttrue
| ST_IszeroSucc : forall t1,
        nvalue t1 ->
        (tiszero (tsucc t1)) ==> tfalse
| ST_Iszero : forall t1 t1',
        t1 ==> t1' ->
        (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse"
    | Case_aux c "ST_If" | Case_aux c "ST_Succ"
    | Case_aux c "ST_PredZero" | Case_aux c "ST_PredSucc"
    | Case_aux c "ST_Pred" | Case_aux c "ST_IszeroZero"
    | Case_aux c "ST_IszeroSucc" | Case_aux c "ST_Iszero" ].

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
    step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Example some_term_is_stuck :
    exists t, stuck t.
Proof.
    exists (tsucc ttrue).
    unfold stuck. split.
    Case "left".
        unfold normal_form. intro contra.
        inversion contra. inversion H. inversion H1.
    Case "right".
        intro contra. inversion contra.
        inversion H. inversion H. inversion H1.
Qed.

Lemma value_is_nf : forall t,
    value t -> step_normal_form t.
Proof.
    unfold normal_form. intros t val contra.
    destruct val as [Hbval | Hnval].
    Case "bvalue".
        induction Hbval;
            (* solves both ttrue and tfalse *)
            inversion contra; inversion H.
    Case "nvalue".
        induction Hnval;
            (* solves tzero and prepares tsucc *)
            inversion contra; inversion H.
        SCase "tsucc".
            apply IHHnval. exists t1'. assumption.
Qed.

Theorem step_deterministic:
    deterministic step.
Proof with eauto.
    unfold deterministic. intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    step_cases (induction Hy1) Case;
        intros y2 Hy2; inversion Hy2; subst;
        try solve [ reflexivity | solve by inversion ].
    Case "ST_If".
        rewrite (IHHy1 t1'0). reflexivity. assumption.
    Case "ST_Succ".
        rewrite (IHHy1 t1'0). reflexivity. assumption.
    Case "ST_PredSucc".
        inversion H1; subst.
        (* t1 is in NF *)
        assert (step_normal_form t1) as t1_NF.
            apply value_is_nf. auto.
        (* and we cannot step from it any further *)
        apply ex_falso_quodlibet.
        apply t1_NF. exists t1'0. assumption.
    Case "ST_Pred".
        SCase "1".
            inversion Hy1; subst.
            assert (step_normal_form y2) as y2_NF.
                apply value_is_nf. auto.
            apply ex_falso_quodlibet.
            apply y2_NF. exists t1'0. assumption.
        SCase "2".
            rewrite (IHHy1 t1'0). reflexivity. assumption.
    Case "ST_IszeroSucc".
        SCase "1".
            inversion H1; subst.
            assert (step_normal_form t1) as t1_NF.
                apply value_is_nf. auto.
            apply ex_falso_quodlibet.
            apply t1_NF. exists t1'0. assumption.
        SCase "2".
            inversion Hy1; subst.
            assert (step_normal_form t0) as t0_NF.
                apply value_is_nf. auto.
            apply ex_falso_quodlibet.
            apply t0_NF. exists t1'0. assumption.
        SCase "3".
            rewrite (IHHy1 t1'0). reflexivity. assumption.
Qed.


