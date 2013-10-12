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

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
    forall (a : aexp), aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
    forall (b : bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
    forall (c : com), cequiv c (ctrans c).

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId i => AId i
  | APlus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 + n2)
      | (a1', a2') => APlus a1' a2'
      end
  | AMinus a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 - n2)
      | (a1', a2') => AMinus a1' a2'
      end
  | AMult a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) => ANum (n1 * n2)
      | (a1', a2') => AMult a1' a2'
      end
  end.

Example fold_aexp_ex1:
    fold_constants_aexp
        (AMult (APlus (ANum 1) (ANum 2)) (AId X))
    = AMult (ANum 3) (AId X).
Proof. reflexivity. Qed.

Example fold_aexp_ex2:
    fold_constants_aexp
      (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
    = AMinus (AId X) (APlus (ANum 0) (AId Y)).
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
              if beq_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BEq a1' a2'
      end
  | BLe a1 a2 =>
      match (fold_constants_aexp a1, fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
              if ble_nat n1 n2 then BTrue else BFalse
      | (a1', a2') => BLe a1' a2'
      end
  | BNot b =>
      match (fold_constants_bexp b) with
      | BTrue => BFalse
      | BFalse => BTrue
      | b1' => BNot b1'
      end
  | BAnd b1 b2 =>
      match (fold_constants_bexp b1, fold_constants_bexp b2) with
      | (BTrue, BTrue) => BTrue
      | (BTrue, BFalse) => BFalse
      | (BFalse, BTrue) => BFalse
      | (BFalse, BFalse) => BFalse
      | (b1', b2') => BAnd b1' b2'
      end
  end.

Example fold_bexp_ex1:
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
    = BTrue.
Proof. reflexivity. Qed.

Example fold_bexp_ex2:
    fold_constants_bexp
      (BAnd (BEq (AId X) (AId Y))
            (BEq (ANum 0)
                 (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
    = BAnd (BEq (AId X) (AId Y)) BTrue.
Proof. reflexivity. Qed.

Fixpoint fold_constants_com (c : com) : com :=
    match c with
    | SKIP => SKIP
    | i ::= a => CAss i (fold_constants_aexp a)
    | c1 ;; c2 =>
          (fold_constants_com c1) ;; (fold_constants_com c2)
    | IFB b THEN c1 ELSE c2 FI =>
          match fold_constants_bexp b with
          | BTrue => fold_constants_com c1
          | BFalse => fold_constants_com c2
          | b' => IFB b' THEN fold_constants_com c1
                         ELSE fold_constants_com c2 FI
          end
    | WHILE b DO c END =>
          match fold_constants_bexp b with
            (* loop with constant true *)
          | BTrue => WHILE BTrue DO SKIP END
            (* just skip with constant false *)
          | BFalse => SKIP
          | b' => WHILE b' DO (fold_constants_com c) END
          end
    end.

Example fold_com_ex1:
    fold_constants_com
      (* original program *)
      (X ::= APlus (ANum 4) (ANum 5);;
       Y ::= AMinus (AId X) (ANum 3);;
       IFB BEq (AMinus (AId X) (AId Y))
               (APlus (ANum 2) (ANum 4))
       THEN
           SKIP
       ELSE
           Y ::= ANum 0
       FI;;
       IFB BLe (ANum 0) (AMinus (ANum 4)
                                (APlus (ANum 2) (ANum 1)))
       THEN
           Y ::= ANum 0
       ELSE 
           SKIP
       FI;;
       WHILE BEq (AId Y) (ANum 0) DO
           X ::= APlus (AId X) (ANum 1)
       END)
    = (* after constant folding *)
      (X ::= ANum 9;;
       Y ::= AMinus (AId X) (ANum 3);;
       IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
           SKIP
       ELSE
           (Y ::= ANum 0)
       FI;;
       Y ::= ANum 0;;
       WHILE BEq (AId Y) (ANum 0) DO
           X ::= APlus (AId X) (ANum 1)
       END).
Proof. reflexivity. Qed.

Theorem fold_constants_aexp_sound :
    atrans_sound fold_constants_aexp.
Proof.
    unfold atrans_sound. intro a. unfold aequiv. intro st.
    aexp_cases (induction a) Case; simpl;
        (* ANum and AId are done with just reflexivity *)
        try reflexivity;
        (* APlus, AMinus, AMult follow from IH *)
        try ( destruct (fold_constants_aexp a1);
              destruct (fold_constants_aexp a2);
              rewrite -> IHa1; rewrite -> IHa2;
              simpl; reflexivity ).
Qed.

Theorem fold_constants_bexp_sound:
    btrans_sound fold_constants_bexp.
Proof.
    unfold btrans_sound. intro b. unfold bequiv. intro st.
    bexp_cases (induction b) Case;
        (* BTrue and BFalse are immediate *)
        try (simpl; reflexivity).
    Case "BEq".
        rename a into a1. rename a0 into a2. simpl. 
        remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
        remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
        replace (aeval st a1) with (aeval st a1') by
            (subst a1'; rewrite <- fold_constants_aexp_sound;
             reflexivity).
        replace (aeval st a2) with (aeval st a2') by
            (subst a2'; rewrite <- fold_constants_aexp_sound;
             reflexivity).
        destruct a1'; destruct a2'; try reflexivity.
           (* remaining case: both a1 and a2 are constants *)
           simpl. destruct (beq_nat n n0); reflexivity.
    Case "BLe".
        rename a into a1. rename a0 into a2. simpl.
        remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
        remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
        replace (aeval st a1) with (aeval st a1') by
            (subst a1'; rewrite <- fold_constants_aexp_sound;
             reflexivity).
        replace (aeval st a2) with (aeval st a2') by
            (subst a2'; rewrite <- fold_constants_aexp_sound;
             reflexivity).
        destruct a1'; destruct a2'; try reflexivity.
            (* remaining case: both a1' a2' constants *)
            simpl. destruct (ble_nat n n0); reflexivity.
    Case "BNot".
        simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
        rewrite -> IHb. destruct b'; try reflexivity.
    Case "BAnd".
        simpl.
        remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
        remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
        rewrite -> IHb1. rewrite -> IHb2.
        destruct b1'; destruct b2'; reflexivity.
Qed. 

Theorem fold_constant_com_sound:
    ctrans_sound fold_constants_com.
Proof.
    unfold ctrans_sound. intro c.
    com_cases (induction c) Case; simpl.
    Case "SKIP". apply refl_cequiv.
    Case "::=".
        apply CAss_congruence. apply fold_constants_aexp_sound.
    Case ";;".
        apply CSeq_congruence; assumption. 
    Case "IFB".
        assert (bequiv b (fold_constants_bexp b)).
            apply fold_constants_bexp_sound.
        destruct (fold_constants_bexp b) eqn:Heqb;
            (* solves most of the goals *)
            try (apply CIf_congruence; assumption).
        SCase "b always true".
            Check trans_cequiv.
            apply trans_cequiv with c1; try assumption. 
            Check IFB_true.
            apply IFB_true; assumption.
        SCase "b alwasy false".
            apply trans_cequiv with c2; try assumption.
            apply IFB_false; assumption. 
    Case "WHILE".
        remember (fold_constants_bexp b) as b' eqn:Heqb'.
        destruct b';
            try (apply CWhile_congruence;
                 try assumption;
                 rewrite -> Heqb';
                 apply fold_constants_bexp_sound).
         SCase "b always true".
             apply WHILE_true. rewrite -> Heqb'.
             apply fold_constants_bexp_sound.
         SCase "b always false". 
             apply WHILE_false. rewrite -> Heqb'.
             apply fold_constants_bexp_sound.
Qed. 

Fixpoint optimize_0plus_aexp (a : aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | AId id => AId id
    | APlus (ANum 0) a2 => a2
    | APlus a1 a2 =>
            APlus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | AMinus a1 a2 =>
            AMinus (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | AMult a1 a2 =>
            AMult (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    end.

Fixpoint optimize_0plus_bexp (b : bexp) : bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 =>
            BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BLe a1 a2 =>
            BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
    | BNot b1 => BNot (optimize_0plus_bexp b1)
    | BAnd b1 b2 =>
            BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2) 
    end.

Fixpoint optimize_0plus_com (c : com) : com :=
    match c with
    | CSkip => CSkip
    | CAss id a => CAss id (optimize_0plus_aexp a)
    | CSeq c1 c2 =>
            CSeq (optimize_0plus_com c1) (optimize_0plus_com c2)
    | CIf b c1 c2 =>
            CIf (optimize_0plus_bexp b)
                (optimize_0plus_com c1)
                (optimize_0plus_com c2)
    | CWhile b c1 =>
            CWhile (optimize_0plus_bexp b) (optimize_0plus_com c1)
    end.

Theorem optimize_0plus_aexp_sound:
    atrans_sound optimize_0plus_aexp.
Proof.
    unfold atrans_sound. intro a. unfold aequiv. intro st.
    aexp_cases (induction a) Case; simpl;
        (* ANum, AId *)
        try reflexivity;
        (* AMinus, AMult *)
        try (rewrite -> IHa1; rewrite -> IHa2; reflexivity). 
    Case "APlus".
        remember (optimize_0plus_aexp a1) as a1'.
        remember (optimize_0plus_aexp a2) as a2'.
        destruct a1; 
           (* most of the cases *)
           try (rewrite -> IHa1; rewrite -> IHa2; reflexivity).
        SCase "ANum". destruct n. 
           (* base *) simpl. reflexivity.
           (* succ *) rewrite -> IHa1. rewrite -> IHa2. reflexivity. 
Qed.

Theorem optimize_0plus_bexp_sound:
    btrans_sound optimize_0plus_bexp.
Proof.
    unfold btrans_sound. intro b. unfold bequiv. intro st.
    bexp_cases (induction b) Case; simpl;
        (* BTrue, BFalse *)
        try reflexivity;
        (* BEq, BLe *)
        (* chaining works because no subgoal are generated *)
        try ( rename a into a1; rename a0 into a2;
              remember (optimize_0plus_aexp a1) as a1';
              remember (optimize_0plus_aexp a2) as a2';
              replace (aeval st a1) with (aeval st a1') by
                  (subst a1'; rewrite <- optimize_0plus_aexp_sound;
                   reflexivity);
              replace (aeval st a2) with (aeval st a2') by
                  (subst a2'; rewrite <- optimize_0plus_aexp_sound;
                   reflexivity);
              reflexivity ).
    Case "BNot". rewrite -> IHb; reflexivity.
    Case "BAnd". rewrite -> IHb1; rewrite -> IHb2; reflexivity.
Qed.

Theorem optimize_0plus_com_sound:
    ctrans_sound optimize_0plus_com.
Proof.
    unfold ctrans_sound. intro c.
    com_cases (induction c) Case; simpl.
    Case "SKIP".
        apply refl_cequiv.
    Case "::=".
        apply CAss_congruence. apply optimize_0plus_aexp_sound.
    Case ";;".
        apply CSeq_congruence; assumption.
    Case "IFB".
        apply CIf_congruence;
            try (apply optimize_0plus_bexp_sound);
            assumption.
    Case "WHILE".
        apply CWhile_congruence;
            try (apply optimize_0plus_bexp_sound);
            assumption.
Qed.

Definition optimizer (c : com) : com :=
    optimize_0plus_com (fold_constants_com c).

Example optimizer_ex1:
    optimizer (X ::= APlus (AMinus (ANum 5) (ANum 5))
                           (AId Z))
    = (X ::= AId Z).
Proof. reflexivity. Qed.

Theorem optimizer_sound:
    ctrans_sound optimizer.
Proof.
    unfold ctrans_sound. intro c. unfold optimizer.
    remember (fold_constants_com c) as c'.
    apply trans_cequiv with c'.
    Case "c to c'".
        rewrite -> Heqc'. apply fold_constant_com_sound.
    Case "c' to (optimize_0plus_com c')".
        apply optimize_0plus_com_sound.
Qed.


