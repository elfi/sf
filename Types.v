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

Inductive ty : Type :=
| TBool : ty
| TNat : ty.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
| T_True :
    |- ttrue \in TBool
| T_False :
    |- tfalse \in TBool
| T_If : forall t1 t2 t3 T,
    |- t1 \in TBool ->
    |- t2 \in T ->
    |- t3 \in T ->
    |- tif t1 t2 t3 \in T
| T_Zero :
    |- tzero \in TNat
| T_Succ : forall t1,
    |- t1 \in TNat ->
    |- tsucc t1 \in TNat
| T_Pred : forall t1,
    |- t1 \in TNat ->
    |- tpred t1 \in TNat
| T_Iszero : forall t1,
    |- t1 \in TNat ->
    |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "T_True" | Case_aux c "T_False"
    | Case_aux c "T_If" | Case_aux c "T_Zero"
    | Case_aux c "T_Succ" | Case_aux c "T_Pred"
    | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

Example has_type_1:
    |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof.
    apply T_If.
        apply T_False.
        apply T_Zero.
        apply T_Succ.
            apply T_Zero.
Qed.

Example has_type_not :
    ~ (|- tif tfalse tzero ttrue \in TBool).
Proof.
    (* first inversion on contra, and then
       inversion on tzero \in TBool *)
    intro contra. solve by inversion 2.
Qed.

Example succ_hastype_nat__hastype_nat : forall t,
    |- tsucc t \in TNat ->
    |- t \in TNat.
Proof.
    intros t H. inversion H. apply H1.
Qed.

Lemma bool_canonical : forall t,
    |- t \in TBool -> value t -> bvalue t.
Proof.
    intros t HT HV. inversion HV.
    Case "H : bvalue t". assumption.
    Case "H : nvalue t". destruct H; solve by inversion.
Qed.

Lemma nat_canonical : forall t,
    |- t \in TNat -> value t -> nvalue t.
Proof.
    intros t HT HV. inversion HV.
    Case "H : bvalue t". destruct H; solve by inversion.
    Case "H : nvalue t". assumption.
Qed.

Theorem progress : forall t T,
    |- t \in T ->
    value t \/ exists t', t ==> t'.
Proof.
    intros t T HT.
    has_type_cases (induction HT) Case; auto.
    Case "T_If".
        right. inversion IHHT1; clear IHHT1.
        SCase "t1 is a value".
            apply (bool_canonical t1 HT1) in H.
            inversion H; subst; clear H.
               exists t2. auto.
               exists t3. auto.
        SCase "t1 can take a step".
            inversion H as [t1' H1].
            exists (tif t1' t2 t3). auto.
    Case "T_Succ".
        inversion IHHT; clear IHHT.
        SCase "t1 is a value".
             left. apply (nat_canonical t1 HT) in H.
             inversion H; subst; clear H; auto.
        SCase "t1 can take a step".
             right.
             inversion H as [t' H1].
             exists (tsucc t'). auto.
    Case "T_Pred".
        right. inversion IHHT; clear IHHT.
        SCase "t1 is a value".
            apply (nat_canonical t1 HT) in H.
            inversion H; subst.
                exists tzero. auto.
                exists t. auto.
        SCase "t1 can take a step".
            inversion H as [t' H1].
            exists (tpred t'). auto.
    Case "T_Iszero".
        right. inversion IHHT; clear IHHT.
        SCase "t1 is a value".
            apply (nat_canonical t1 HT) in H.
            inversion H; subst.
                exists ttrue. auto.
                eexists. auto. (* more automation *)
        SCase "t1 can take a step".
            inversion H as [t' H1].
            eexists. eauto. (* yet more automation *)
Qed.

Theorem preservation : forall t t' T,
    |- t \in T ->
    t ==> t' ->
    |- t' \in T.
Proof.
    intros t t' T HT HE.
    generalize dependent t'.
    has_type_cases (induction HT) Case;
        intros t' HE;
        try solve by inversion.
    Case "T_If".
        inversion HE; subst; clear HE.
        SCase "ttrue". assumption.
        SCase "tfalse". assumption.
        SCase "tif". apply T_If; try assumption.
            apply IHHT1. assumption.
    Case "T_Succ".
        inversion HE; subst; clear HE.
        apply IHHT in H0. apply T_Succ. assumption.
    Case "T_Pred".
        inversion HE; subst; clear HE.
        SCase "tzero". apply T_Zero.
        SCase "tsucc". inversion HT; subst. assumption.
        SCase "t1". apply T_Pred. apply IHHT. assumption.
    Case "T_Iszero".
        inversion HE; subst; clear HE;
        (* constructors, inductive hypothesis, assumption *)
        auto.
Qed.

Theorem preservation' : forall t t' T,
    |- t \in T ->
    t ==> t' ->
    |- t' \in T.
Proof.
    intros t t' T HT HE. generalize dependent T.
    step_cases (induction HE) Case;
        intros T HT;
        inversion HT; subst; clear HT;
        try auto.
    Case "ST_PredSucc".
        inversion H1; auto.
Qed.


