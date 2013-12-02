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

Module Temp2.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_Funny : forall n,
        C n ==> P (C n) (C 0)
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

Lemma value_not_same_as_normal_form :
    exists v, value v /\ ~ normal_form step v.
Proof.
    exists (C 1).
    split.
    Case "left".
        apply v_const.
    Case "right".
        unfold normal_form. intro contra. apply contra.
        exists (P (C 1) (C 0)). apply ST_Funny.
Qed.

End Temp2.

Module Temp3.

Inductive value : tm -> Prop :=
| v_const : forall n, value (C n).

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_PlusConstConst : forall n1 n2,
        P (C n1) (C n2) ==> C (n1 + n2)
| ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        P t1 t2 ==> P t1' t2

where " t '==>' t' " := (step t t').

Lemma value_not_same_as_normal_form :
    exists t, ~ value t /\ normal_form step t.
Proof.
    exists (P (C 1) (P (C 2) (C 3))).
    split.
    Case "left".
        intro contra. inversion contra.
    Case "right".
        unfold normal_form. intro contra.
        inversion contra. inversion H. inversion H3.
Qed.

End Temp3.

Module Temp4.

Inductive tm : Type :=
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.

Inductive value : tm -> Prop :=
| v_true : value ttrue
| v_false : value tfalse.

Reserved Notation " t '==>' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_IfTrue : forall t1 t2,
        tif ttrue t1 t2 ==> t1
| ST_IfFalse : forall t1 t2,
        tif tfalse t1 t2 ==> t2
| ST_If : forall t1 t1' t2 t3,
        t1 ==> t1' ->
        tif t1 t2 t3 ==> tif t1' t2 t3

where " t '==>' t' " := (step t t').

Definition bool_step_prop1 :=
    tfalse ==> tfalse.

Theorem bool_step_prop1_false: ~bool_step_prop1.
Proof.
    unfold bool_step_prop1. intro contra. inversion contra.
Qed.

Definition bool_step_prop2 :=
    tif ttrue
        (tif ttrue ttrue ttrue)
        (tif tfalse tfalse tfalse)
    ==> ttrue.

Theorem bool_step_prop2_false : ~bool_step_prop2.
Proof.
    unfold bool_step_prop2. intro contra. inversion contra.
Qed.

Definition bool_step_prop3 :=
    tif (tif ttrue ttrue ttrue)
        (tif ttrue ttrue ttrue)
        tfalse
    ==>
    tif ttrue
        (tif ttrue ttrue ttrue)
        tfalse.

Theorem bool_step_prop3_true : bool_step_prop3.
Proof.
    unfold bool_step_prop3.
    apply ST_If. apply ST_IfTrue.
Qed.

Theorem strong_progress : forall t,
    value t \/ (exists t', t ==> t').
Proof.
    induction t.
    Case "ttrue". left. apply  v_true.
    Case "tfalse". left. apply v_false.
    Case "tif".
        inversion IHt1.
        SCase "value t1".
            (* which value *)
            inversion H.
            SSCase "ttrue". right. exists t2. apply ST_IfTrue.
            SSCase "tfalse". right. exists t3. apply ST_IfFalse.
        SCase "exists t', t1 ==> t'".
            (* what t' *)
            inversion H.
            right. exists (tif x t2 t3). apply ST_If.
            assumption.
Qed.

Theorem step_deterministic :
    deterministic step.
Proof.
    unfold deterministic. intros x y1 y2 Hy1 Hy2.
    generalize dependent y2.
    induction Hy1; intros y2 Hy2.
    Case "ttrue".
        inversion Hy2.
        reflexivity. inversion H3.
    Case "tfalse".
        inversion Hy2.
        reflexivity. inversion H3.
    Case "tif".
        inversion Hy2.
        SCase "t1 = ttrue".
            rewrite <- H0 in Hy1. inversion Hy1.
        SCase "t1 = tfalse".
            rewrite <- H0 in Hy1. inversion Hy1.
        SCase "t1 ==> t1'0".
            rewrite -> (IHHy1 t1'0). reflexivity.
            assumption.
Qed.

Module Temp5.

Reserved Notation " t '==' t' " (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_IfTrue : forall t1 t2,
        tif ttrue t1 t2 ==> t1
| ST_IfFalse : forall t1 t2,
        tif tfalse t1 t2 ==> t2
| ST_If : forall t1 t1' t2 t3,
        t1 ==> t1' ->
        tif t1 t2 t3 ==> tif t1' t2 t3
| ST_IfShort : forall t1 t2,
        value t2 ->
        tif t1 t2 t2 ==> t2

where " t '==>' t' " := (step t t').

Definition bool_step_prop4 :=
    tif (tif ttrue ttrue ttrue)
        tfalse
        tfalse
    ==>
    tfalse.

Example bool_step_prop4_holds: bool_step_prop4.
Proof.
    unfold bool_step_prop4.
    apply ST_IfShort. apply v_false.
Qed.

Theorem bool_with_shortcut_step_not_deterministic:
    ~(deterministic step).
Proof.
    unfold deterministic. intro contra.
    remember (tif (tif ttrue ttrue ttrue)
                  tfalse
                  tfalse) as t.
    assert (H1: t ==> tfalse).
       rewrite Heqt. apply ST_IfShort. apply v_false.
    assert (H2: t ==> (tif ttrue tfalse tfalse)).
       rewrite Heqt. apply ST_If. apply ST_IfTrue.
    remember (contra t tfalse (tif ttrue tfalse tfalse)
                     H1 H2) as H3.
    inversion H3.
Qed.

Theorem bool_with_shortcut_strong_progress:
    forall t, value t \/ (exists t', t ==> t').
Proof.
    (* it holds as before, we use establised evaluation paths *)
    induction t.
    Case "ttrue". left. apply v_true.
    Case "tfalse". left. apply v_false.
    Case "tif".
        inversion IHt1.
        SCase "value t1".
            inversion H.
            SSCase "ttrue". right. exists t2. apply ST_IfTrue.
            SSCase "tfalse". right. exists t3. apply ST_IfFalse.
        SCase "exists t', t1 ==> t'".
            inversion H.
            right. exists (tif x t2 t3).
            apply ST_If. assumption.
Qed.

End Temp5.
End Temp4.

Inductive multi {X:Type} (R: relation X) : relation X :=
| multi_refl : forall (x:X), multi R x x
| multi_step : forall (x y z : X),
        R x y ->
        multi R y z ->
        multi R x z.

Tactic Notation "multi_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Definition multistep := multi step.
Notation " t '==>*' t' " := (multistep t t') (at level 40).

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
    R x y -> (multi R) x y.
Proof.
    intros X R x y H. apply multi_step with y.
    apply H. apply multi_refl.
Qed.

Theorem multi_trans:
    forall (X:Type) (R:relation X) (x y z : X),
    multi R x y ->
    multi R y z ->
    multi R x z.
Proof.
    intros X R x y z G H.
    multi_cases (induction G) Case.
    Case "multi_refl". assumption.
    Case "multi_step".
        apply multi_step with y. assumption.
        apply IHG. assumption.
Qed.

Lemma test_multistep_1:
    P (P (C 0) (C 3))
      (P (C 2) (C 4))
    ==>*
    C ((0 + 3) + (2 + 4)).
Proof.
    apply multi_step with
        (P (C (0 + 3))
           (P (C 2) (C 4))).
    apply ST_Plus1. apply ST_PlusConstConst.
    apply multi_step with
        (P (C (0 + 3))
           (C (2 + 4))).
    apply ST_Plus2. apply v_const. apply ST_PlusConstConst.
    apply multi_R.
    apply ST_PlusConstConst.
Qed.

Lemma test_multistep_1':
    P (P (C 0) (C 3))
      (P (C 2) (C 4))
    ==>*
    C ((0 + 3) + (2 + 4)).
Proof.
    eapply multi_step.
        apply ST_Plus1. apply ST_PlusConstConst.
    eapply multi_step.
        apply ST_Plus2. apply v_const. apply ST_PlusConstConst.
    eapply multi_step.
        apply ST_PlusConstConst.
    apply multi_refl.
Qed.

Lemma test_multistep_3:
    P (C 0) (C 3)
    ==>*
    P (C 0) (C 3).
Proof.
    apply multi_refl.
Qed.

Lemma test_multistep_4:
    P (C 0)
      (P (C 2)
         (P (C 0) (C 3)))
    ==>*
    P (C 0)
      (C (2 + (0 + 3))).
Proof.
    eapply multi_step.
        apply ST_Plus2. apply v_const.
        apply ST_Plus2. apply v_const.
        apply ST_PlusConstConst.
    eapply multi_step.
        apply ST_Plus2. apply v_const.
        apply ST_PlusConstConst.
    apply multi_refl.
Qed.


