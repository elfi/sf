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

Theorem assign_aequiv: forall X e,
    aequiv (AId X) e ->
    cequiv SKIP (X ::= e).
Proof.
    intros X e Hae. split; intro H.
    Case "->".
        inversion H; subst.
        assert (st' = (update st' X (st' X))).
        SCase "Proof of assert".
            apply functional_extensionality; intro x.
            rewrite -> update_same; reflexivity.
        rewrite -> H0 at 2.
        apply E_Ass.
        unfold aequiv in Hae. simpl in Hae.
        rewrite -> Hae. reflexivity.
    Case "<-".
        inversion H; subst.  
        assert (st = (update st X (aeval st e))).
        SCase "Proof of assert".
            apply functional_extensionality; intro x.
            unfold aequiv in Hae; simpl in Hae.
            rewrite <- Hae. rewrite -> update_same; reflexivity.
        rewrite <- H0. apply E_Skip.
Qed.

Lemma refl_aequiv: forall (a: aexp), aequiv a a.
Proof. intro a. unfold aequiv. intro st. reflexivity. Qed.

Lemma sym_aequiv: forall (a1 a2 : aexp),
    aequiv a1 a2 -> aequiv a2 a1.
Proof. unfold aequiv. intros a1 a2 H. symmetry. apply H. Qed.

Lemma trans_aequiv: forall (a1 a2 a3 : aexp),
    aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
    unfold aequiv. intros a1 a2 a3 H1 H2. intro st.
    rewrite -> H1. rewrite -> H2. reflexivity.
Qed.

Lemma refl_bequiv: forall (b : bexp), bequiv b b.
Proof. intro b. unfold bequiv. reflexivity. Qed.

Lemma sym_bequiv: forall (b1 b2 : bexp), 
    bequiv b1 b2 -> bequiv b2 b1.
Proof. intros b1 b2 H st. symmetry. apply H. Qed.

Lemma trans_bequiv: forall (b1 b2 b3 : bexp),
    bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
    intros b1 b2 b3 H1 H2 st.
    rewrite -> H1. rewrite -> H2. reflexivity.
Qed.

Lemma refl_cequiv: forall (c : com), cequiv c c.
Proof. unfold cequiv. intros c st st'. apply iff_refl. Qed.

Lemma sym_cequiv: forall (c1 c2 : com), 
    cequiv c1 c2 -> cequiv c2 c1.
Proof. intros c1 c2 H st st'. apply iff_sym. apply H. Qed.

Lemma iff_trans: forall (P1 P2 P3 : Prop),
    (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
    intros. inversion H. inversion H0.
    split; intro A.
        apply H3. apply H1. apply A.
        apply H2. apply H4. apply A.
Qed.

Lemma trans_cequiv: forall (c1 c2 c3 : com),
    cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
    unfold cequiv. intros c1 c2 c3 H1 H2 st st'.
    apply iff_trans with (c2 / st || st'). apply H1. apply H2.
Qed.

Theorem CAss_congruence : forall i a1 a1',
    aequiv a1 a1' ->
    cequiv (CAss i a1) (CAss i a1').
Proof.
    intros i a1 a1' Heqv st st'.
    split; intro Hceval.
    Case "->". inversion Hceval; subst.
        apply E_Ass. symmetry. apply Heqv.
    Case "<-". inversion Hceval; subst.
        apply E_Ass. apply Heqv.
Qed.

Theorem CWhile_congruence: forall b1 b1' c1 c1',
    bequiv b1 b1' -> cequiv c1 c1' ->
    cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
    unfold bequiv, cequiv.
    intros b1 b1' c1 c1' Hb1e Hc1e st st'.
    split; intros Hce.
    Case "->".
        remember (WHILE b1 DO c1 END) as cwhile eqn:Heqcwhile.
        induction Hce; inversion Heqcwhile; subst.
        SCase "E_WhileEnd".
            apply E_WhileEnd. rewrite <- Hb1e. assumption.
        SCase "E_WhileLoop".
            apply E_WhileLoop with st'.
            SSCase "Loop runs b condition".
                rewrite <- Hb1e. assumption.
            SSCase "Body execution".
                apply (Hc1e st st'). assumption.
            SSCase "Subsequent loop execution".
                apply IHHce2. assumption.
    Case "<-".
        remember (WHILE b1' DO c1' END) as c'while eqn:Heqc'while.
        induction Hce; inversion Heqc'while; subst.
        SCase "E_WhileEnd".
            apply E_WhileEnd. rewrite -> Hb1e. assumption.
        SCase "E_WhileLoop".
            apply E_WhileLoop with st'. 
            SSCase "Loop runs b condition".
                rewrite -> Hb1e. assumption.
            SSCase "Body execution".
                apply (Hc1e st st'). assumption.
            SSCase "Subsequent loop execution".
                apply IHHce2. assumption.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
    cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (c1;;c2) (c1';;c2').
Proof.
    unfold cequiv. intros c1 c1' c2 c2' Hc1e Hc2e st st'.
    split; intro H; subst.
    Case "->".
        inversion H; subst.
        apply E_Seq with st'0.
        SSCase "c1'". rewrite <- Hc1e. assumption.
        SSCase "c2'". rewrite <- Hc2e. assumption.
    Case "<-".
        inversion H; subst.
        apply E_Seq with st'0.
        SSCase "c1". rewrite -> Hc1e. assumption.
        SSCase "c2". rewrite -> Hc2e. assumption.
Qed.

Theorem CIf_congruence: forall b b' c1 c1' c2 c2',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (IFB b  THEN c1  ELSE c2  FI)
           (IFB b' THEN c1' ELSE c2' FI).
Proof.
    unfold bequiv, cequiv. 
    intros b b' c1 c1' c2 c2' Hbe Hc1e Hc2e st st'.
    split; intro H; subst.
    Case "->".
        inversion H; subst.
        SCase "b = true".
            apply E_IfTrue. 
            SSCase "condition". rewrite <- Hbe. assumption.
            SSCase "command". rewrite <- Hc1e. assumption.
        SCase "b = false".
            apply E_IfFalse.
            SSCase "condition". rewrite <- Hbe. assumption.
            SSCase "command". rewrite <- Hc2e. assumption.
    Case "<-".
        inversion H; subst.
        SCase "b' = true".
            apply E_IfTrue.
            SSCase "condition". rewrite -> Hbe. assumption.
            SSCase "command". rewrite -> Hc1e. assumption.
        SCase "b' = false".
            apply E_IfFalse.
            SSCase "condition". rewrite -> Hbe. assumption.
            SSCase "command". rewrite -> Hc2e. assumption.
Qed.

Example congruence_example:
    cequiv
      (* program 1 *)
      (X ::= ANum 0;;
       IFB (BEq (AId X) (ANum 0))
       THEN 
         Y ::= ANum 0
       ELSE 
         Y ::= ANum 42
       FI)
       (* program 2 *)
       (X ::= ANum 0;;
        IFB (BEq (AId X) (ANum 0))
        THEN
          Y ::= AMinus (AId X) (AId X)
        ELSE
          Y ::= ANum 42
        FI).
Proof.
    apply CSeq_congruence.
        apply refl_cequiv.
        apply CIf_congruence.
          apply refl_bequiv.
          apply CAss_congruence. unfold aequiv. simpl.
              symmetry. apply minus_diag.
          apply refl_cequiv.
Qed.


