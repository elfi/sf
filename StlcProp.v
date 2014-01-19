Require Export Stlc.

Module STLCProp.
Import STLC.

Lemma cannonical_forms_bool: forall t,
    empty |- t \in TBool ->
    value t ->
    (t = ttrue) \/ (t = tfalse).
Proof.
    intros t HT HVal.
    inversion HVal; subst; try inversion HT; auto.
Qed.

Lemma cannonical_forms_fun : forall t T1 T2,
    empty |- t \in (TArrow T1 T2) ->
    value t ->
    exists x u, t = tabs x T1 u.
Proof.
    intros t T1 T2 HT HVal.
    inversion HVal; subst; inversion HT.
    subst. exists x0. exists t0. reflexivity.
Qed.

Theorem progress: forall t T,
    empty |- t \in T ->
    value t \/ exists t', t ==> t'.
Proof.
    intros t T Ht.
    remember (@empty ty) as Gamma.
    has_type_cases (induction Ht) Case; subst Gamma; auto.
    Case "T_Var".
        inversion H.
    Case "T_App".
        right. destruct IHHt1. reflexivity.
        SCase "tt is a value".
            destruct IHHt2. reflexivity.
            SSCase "t1 is also a value".
                assert (exists x0 t0, tt = tabs x0 T1 t0).
                eapply cannonical_forms_fun; eassumption.
                destruct H1 as [x0 [t0 Heq]]. subst.
                exists ([x0:=t1]t0). auto.
            SSCase "t1 steps".
                inversion H0 as [t1' Hstp].
                exists (tapp tt t1'). auto.
        SCase "tt steps".
            inversion H as [tt' Hstp].
            exists (tapp tt' t1). auto.
    Case "T_If".
        right. destruct IHHt1; auto.
        SCase "t1 is a value".
            destruct (cannonical_forms_bool t1);
              subst; eauto.
        SCase "t1 steps".
            inversion H as [t1' Hstp].
            exists (tif t1' t2 t3). auto.
Qed.

Theorem progress' : forall t T,
    empty |- t \in T ->
    value t \/ exists t', t ==> t'.
Proof.
    intros t.
    t_cases (induction t) Case; intros T Ht; auto.
    Case "tvar".
        right. inversion Ht. subst. inversion H1.
    Case "tapp".
        right. inversion Ht. subst.
        destruct (IHt1 (TArrow T1 T));
          subst; eauto.
        SCase "t1 is a value".
            destruct (IHt2 T1); subst; auto.
            SSCase "t2 is also a value".
                assert (exists x0 t0, t1 = tabs x0 T1 t0).
                eapply cannonical_forms_fun; eassumption.
                destruct H1 as [x0 [t0 Heq]]. subst.
                exists ([x0:=t2]t0). auto.
            SSCase "t2 steps".
                inversion H0 as [t2' Hstp].
                exists (tapp t1 t2'); auto.
        SCase "t1 steps".
            inversion H as [t1' Hstp].
            exists (tapp t1' t2). auto.
    Case "tif".
        right. inversion Ht. subst.
        destruct (IHt1 TBool). auto.
        SCase "t1 is a value".
            destruct (cannonical_forms_bool t1);
              subst; eauto.
        SCase "t1 steps".
            inversion H as [t1' Hstp].
            exists (tif t1' t2 t3). auto.
Qed.

Inductive appears_free_in : id -> tm -> Prop :=
| afi_var : forall x,
        appears_free_in x (tvar x)
| afi_app1 : forall x t1 t2,
        appears_free_in x t1 ->
        appears_free_in x (tapp t1 t2)
| afi_app2 : forall x t1 t2,
        appears_free_in x t2 ->
        appears_free_in x (tapp t1 t2)
| afi_abs : forall x y T t,
        y <> x ->
        appears_free_in x t ->
        appears_free_in x (tabs y T t)
| afi_if1 : forall x t1 t2 t3,
        appears_free_in x t1 ->
        appears_free_in x (tif t1 t2 t3)
| afi_if2 : forall x t1 t2 t3,
        appears_free_in x t2 ->
        appears_free_in x (tif t1 t2 t3)
| afi_if3 : forall x t1 t2 t3,
        appears_free_in x t3 ->
        appears_free_in x (tif t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "afi_var" | Case_aux c "afi_app1"
    | Case_aux c "afi_app2" | Case_aux c "afi_abs"
    | Case_aux c "aif_if1" | Case_aux c "aif_if2"
    | Case_aux c "aif_if3" ].

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
    forall x, ~ appears_free_in x t.

