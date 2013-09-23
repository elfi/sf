Require Export Imp.

(* equivalence of expressions *)

Definition aequiv (a1 a2 : aexp) : Prop :=
    forall (st : state),
        aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
    forall (st : state),
        beval st b1 = beval st b2.

(* equivalence of programs *)

Definition cequiv (c1 c2 : com) : Prop :=
    forall (st st' : state),
        (c1 / st || st') <-> (c2 / st || st').

Theorem aequiv_example:
    aequiv (AMinus (AId X) (AId X)) (ANum 0).
Proof.
    unfold aequiv. intros. simpl. omega.
Qed.

Theorem bequiv_example:
    bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
Proof.
    unfold bequiv. intros. simpl.
    assert (st X - st X = 0). omega.
    rewrite -> H. reflexivity.
Qed.

Theorem skip_left: forall c,
    cequiv (SKIP;; c) c.
Proof.
    unfold cequiv. intros c st st'. split.
    Case "->".
        intro H. inversion H. subst.
        inversion H2. subst. assumption.
    Case "<-".
        intro H. apply E_Seq with st.
        apply E_Skip. apply H.
Qed.

Theorem skip_right: forall c,
    cequiv (c;; SKIP) c.
Proof.
    unfold cequiv. intros c st st'. split.
    Case "->".
        intro H. inversion H. subst.
        inversion H5. subst. assumption.
    Case "<-".
        intro H. apply E_Seq with st'.
        apply H. apply E_Skip.
Qed.

Theorem IFB_true_simple: forall c1 c2,
    cequiv (IFB BTrue THEN c1 ELSE c2 FI) c1.
Proof.
    unfold cequiv. intros c1 c2 st st'. split.
    Case "->".
        intro H. inversion H. 
        subst. assumption.
        subst. inversion H5.
    Case "<-".
        intro H. apply E_IfTrue.
        simpl. reflexivity.
        assumption.
Qed.

Theorem IFB_true: forall b c1 c2,
    bequiv b BTrue ->
    cequiv (IFB b THEN c1 ELSE c2 FI) c1.
Proof.
    intros b c1 c2 HbEqBtrue. unfold cequiv. split.
    Case "->".
        intro H. inversion H. 
            subst. assumption.
            subst. unfold bequiv in HbEqBtrue.
            rewrite -> HbEqBtrue in H5. inversion H5.
    Case "<-".
        intro H. apply E_IfTrue.
            unfold bequiv in HbEqBtrue.
            rewrite -> HbEqBtrue. simpl. reflexivity.
            assumption.            
Qed.

Theorem IFB_false: forall b c1 c2,
    bequiv b BFalse ->
    cequiv (IFB b THEN c1 ELSE c2 FI) c2.
Proof.
    intros b c1 c2 HbEqF. split; intros H.
    Case "->".
        inversion H; subst; try assumption.
            (* contradictive subgoal *)
            rewrite HbEqF in H5; inversion H5.
    Case "<-".
        apply E_IfFalse; try assumption.
            (* just rewrite to finish *)
            rewrite HbEqF; reflexivity.
Qed.

Theorem swap_if_branches: forall b e1 e2,
    cequiv
      (IFB b THEN e1 ELSE e2 FI)
      (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
    intros b e1 e2. split; intro H.
    Case "->".
        inversion H; subst.
          apply E_IfFalse; try assumption.
             simpl. rewrite -> H5. reflexivity.
          apply E_IfTrue; try assumption.
             simpl. rewrite -> H5. reflexivity.
    Case "<-".
        inversion H; subst.
          apply E_IfFalse; try assumption.
             simpl in H5.
             rewrite -> negb_true_iff in H5. assumption. 
          apply E_IfTrue; try assumption.
             simpl in H5.
             rewrite -> negb_false_iff in H5. assumption.
Qed.

Theorem WHILE_false: forall b c,
    bequiv b BFalse ->
    cequiv (WHILE b DO c END) SKIP.
Proof.
    intros b c Hb. split; intro H.
    Case "->".
        inversion H; subst.
        SCase "E_WhileEnd".
            apply E_Skip.
        SCase "E_WhileLoop".
            unfold bequiv in Hb. rewrite Hb in H2. inversion H2.
    Case "<-".
        inversion H; subst.
        apply E_WhileEnd. unfold bequiv in Hb. rewrite -> Hb.
        simpl. reflexivity.
Qed.

Lemma WHILE_true_nonterm: forall b c st st',
    bequiv b BTrue ->
    ~( (WHILE b DO c END) / st || st' ).
Proof.
    intros b c st st' Hb.
    intro H.
    remember (WHILE b DO c END) as cw eqn:Heqcw.
    ceval_cases (induction H) Case;
    (* most cases don't apply and can be clear out be inversion *)
        inversion Heqcw; subst; clear Heqcw.
    Case "E_WhileEnd".
        unfold bequiv in Hb. rewrite Hb in H. inversion H.
    Case "E_WhileLoop".
        apply IHceval2. reflexivity. 
Qed.

Theorem WHILE_true: forall b c,
    bequiv b BTrue ->
    cequiv
        (WHILE b DO c END)
        (WHILE BTrue DO SKIP END).
Proof.
    intros b c Hb. split; intro H.
    Case "->".
       (* in the Hb context, H cannot be true, ~H actually is *)
       assert (~(WHILE b DO c END) / st || st').
       SCase "Proof of assert".
           apply WHILE_true_nonterm.
           unfold bequiv. assumption.
       apply H0 in H. inversion H.
    Case "<-".
        (* H is obviously not true, but ~H is *)
        assert (~(WHILE BTrue DO SKIP END) / st || st').
        SCase "Proof of assert".
            apply WHILE_true_nonterm. unfold bequiv. reflexivity.
        apply H0 in H. inversion H.
Qed.

Theorem loop_unrolling: forall b c,
    cequiv
        (WHILE b DO c END)
        (IFB b THEN (c;; WHILE b DO c END) ELSE SKIP FI).
Proof.
    intros b c. split; intro Hce.
    Case "->".
        inversion Hce; subst.
        SCase "E_WhileEnd". apply E_IfFalse.
            assumption.
            apply E_Skip.
        SCase "E_WhileLoop". apply E_IfTrue.
            assumption.
            apply E_Seq with st'0. assumption. assumption.
    Case "<-".
        inversion Hce; subst.
        SCase "b is true, ie loop runs". inversion H5; subst.
            apply E_WhileLoop with st'0. assumption. assumption.
            assumption.
        SCase "b is false, in loop ends". inversion H5; subst.
            apply E_WhileEnd. assumption.
Qed.

Theorem seq_assoc: forall c1 c2 c3,
    cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)).
Proof.
    intros c1 c2 c3. split; intro H.
    Case "->".
        inversion H; subst. inversion H2; subst.
        apply E_Seq with st'1.
          assumption.
          apply E_Seq with st'0. assumption. assumption.
    Case "<-".
        inversion H; subst. inversion H5; subst.
        apply E_Seq with st'1.
          apply E_Seq with st'0. assumption. assumption.
          assumption.
Qed.

Axiom functional_extensionality:
    forall {X Y : Type} {f g : X -> Y},
    (forall (x:X), f x = g x) -> f = g.

Theorem identity_assignment: forall (X:id),
    cequiv (X ::= AId X) SKIP.
Proof.
    intros. split; intro H.
    Case "->".
        inversion H; subst. simpl. simpl in H.
        replace (update st X (st X)) with st. constructor.
        apply functional_extensionality.
        intro x.
        Check update_same.
        rewrite -> update_same. reflexivity. reflexivity.
    Case "<-".
        inversion H; subst.
        (* need to rewrite goal so that E_Ass can be applied *)
        assert (st' = (update st' X (st' X))).
        SCase "Proof of assert".
            apply functional_extensionality. intro x.
            rewrite -> update_same; reflexivity.
        rewrite H0 at 2. (* rewrite the second occurence of st' *)
        apply E_Ass. simpl. reflexivity.
Qed.


