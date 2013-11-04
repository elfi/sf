Require Export Imp.

Definition Assertion := state -> Prop.

Module ExAssertions.

Definition as1: Assertion := fun st => st X = 3.
Definition as2: Assertion := fun st => st X <= st Y.
Definition as3: Assertion :=
    fun st => st X = 3 \/ st X <= st Y.
Definition as4: Assertion :=
    fun st => st Z * st Z <= st X /\
        ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition as5 : Assertion := fun st => True.
Definition as6 : Assertion := fun st => False.

Print False.

Definition assert_implies (P Q : Assertion) : Prop :=
    forall st, P st -> Q st.

Notation "P ->> Q" :=
    (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
    (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition hoare_triple
    (P : Assertion) (c : com) (Q : Assertion) : Prop :=
    forall st st',
        c / st || st' ->
        P st ->
        Q st'.

Notation "{{ P }} c {{ Q }}" :=
    (hoare_triple P c Q) (at level 90, c at next level)
    : hoare_spec_scope.

Theorem hoare_post_true: forall (P Q : Assertion) c,
    (forall st, Q st) ->
    {{ P }} c {{ Q }}.
Proof.
    intros P Q c H. unfold hoare_triple.
    intros st st' Heval HP.
    apply H.
Qed.

Theorem hoare_pre_false: forall (P Q : Assertion) c,
    (forall st, ~(P st)) ->
    {{ P }} c {{ Q }}.
Proof.
    intros P Q c H. unfold hoare_triple.
    intros st st' Heval HP. apply H in HP.
    inversion HP.
Qed.

Definition assn_sub X a P : Assertion :=
    fun (st : state) =>
    P (update st X (aeval st a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn: forall Q X a,
    {{ Q [X |-> a] }} (X ::= a) {{ Q }}.
Proof.
    intros Q X a. unfold hoare_triple.
    intros st st' Heval HQ'.
    inversion Heval. subst.
    unfold assn_sub in HQ'. assumption.
Qed.

Example assn_sub_example:
    {{ (fun st => st X = 3) [ X |-> ANum 3 ] }}
    (X ::= ANum 3)
    {{ fun st => st X = 3 }}.
Proof. apply hoare_asgn. Qed.

Example hoare_asgn_examples_ex1:
    {{ (fun st => st X <= 5) [ X |-> APlus (AId X) (ANum 1) ] }}
    (X ::= APlus (AId X) (ANum 1))
    {{ (fun st => st X <= 5) }}.
Proof. apply hoare_asgn. Qed.

Example hoare_asgn_examples_ex2:
    {{ (fun st => (0 <= st X /\ st X <= 5)) [ X |-> ANum 3 ] }}
    (X ::= ANum 3)
    {{ (fun st => (0 <= st X /\ st X <= 5)) }}.
Proof. apply hoare_asgn. Qed.

Theorem hoare_asgn_fwd:
    (forall {X Y : Type} {f g : X -> Y},
       (forall (x:X), f x = g x) -> f = g) ->
    forall m a Q,
    {{ fun st => Q st /\ st X = m }}
    X ::= a
    {{ fun st => Q (update st X m) /\ 
                 st X = aeval (update st X m) a }}.
Proof.
    intros functional_extensionality m a Q.
    unfold hoare_triple. intros st st' Heval HQm.
    inversion HQm.
    inversion Heval. subst.
    assert (Hst: st = update (update st X (aeval st a)) X (st X)).
        apply functional_extensionality. intro x.
        rewrite -> update_shadow. rewrite -> update_same;
        reflexivity.
    rewrite <- Hst.
    split.
    Case "left". assumption.
    Case "right". unfold update. simpl. reflexivity.
Qed.

Theorem hoare_consequence_pre: forall (P P' Q : Assertion) c,
    {{ P' }} c {{ Q }} ->
    P ->> P' ->
    {{ P }} c {{ Q }}.
Proof.
    intros P P' Q c Hhoare Himp. unfold hoare_triple.
    intros st st' Hc HP. apply (Hhoare st st').
    assumption.
    apply Himp. assumption.
Qed.

Theorem hoare_consequence_post: forall (P Q Q' : Assertion) c,
    {{ P }} c {{ Q' }} ->
    Q' ->> Q ->
    {{ P }} c {{ Q }}.
Proof.
    intros P Q Q' c Hhoare Himp. unfold hoare_triple.
    intros st st' Hc HP. apply Himp. apply (Hhoare st st').
    assumption. assumption.
Qed.

Example hoare_asgn_example1:
    {{ fun st => True }}
    X ::= (ANum 1)
    {{ fun st => st X = 1 }}.
Proof.
    apply hoare_consequence_pre
        with (P' := (fun st => st X = 1) [ X |-> ANum 1] ).
    apply hoare_asgn.
    unfold assert_implies. intros st Htrue.
    unfold assn_sub. unfold update. simpl. reflexivity.
Qed.

Theorem hoare_consequence: forall (P P' Q Q' : Assertion) c,
    {{ P' }} c {{ Q' }} ->
    P ->> P' ->
    Q' ->> Q ->
    {{ P }} c {{ Q }}.
Proof.
    intros P P' Q Q' c Hhoare HPimp HQimp. unfold hoare_triple.
    intros st st' Hceval HP.
    apply HQimp. apply (Hhoare st st').
    assumption.
    apply HPimp. assumption.
    (* or use:
       apply hoare_consequence_pre with (P' := P')
       apply hoare_consequence_post with (Q' := Q') *)
Qed.

Example hoare_asgn_examples_ex1' :
    {{ fun st => True }}
    X ::= ANum 1
    {{ fun st => st X = 1 }}.
Proof.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold assert_implies. intros st H. reflexivity.
Qed.

Example silly1: forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (forall x y : nat, P x y) ->
    (forall x y : nat, P x y -> Q x) ->
    Q 42.
Proof.
    intros P Q HP HQ. eapply HQ. apply HP. 
    (* What should y be? *)
    (* Qed. => Error: Attempt to save a proof with
               existential variables still non-instantiated *)
Abort.

Lemma silly2:
    forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (exists y, P 42 y) ->
    (forall x y : nat, P x y -> Q x) ->
    Q 42.
Proof.
    intros P Q HP HQ. destruct HP as [y HP'].
    (* y has been brought to the env. before eapply creates
       existential variables => can be later used to instantiate
       this ex. variable *)
    eapply HQ. apply HP'.
Qed.

Lemma silly2_eassumption: forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (exists y, P 42 y) ->
    (forall x y : nat, P x y -> Q x) ->
    Q 42.
Proof.
    intros P Q HP HQ. destruct HP as [y HP'].
    eapply HQ. eassumption.
Qed.

Example hoare_asgn_examples_examples_2_1:
    {{ (fun st => st X <= 5) [ X |-> (APlus (AId X) (ANum 1)) ] }}
    X ::= (APlus (AId X) (ANum 1))
    {{ fun st => st X <= 5 }}.
Proof. apply hoare_asgn. Qed.

Example hoare_asgn_examples_examples_2_2:
    {{ (fun st => (0 <= 3 /\ 3 <= 5)) }}
    X ::= ANum 3
    {{ (fun st => (0 <= st X /\ st X <= 5)) }}.
Proof.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold assert_implies. intros st H.
    unfold assn_sub. simpl.
    unfold update. simpl. assumption.
Qed.

Theorem hoare_skip: forall P,
    {{ P }} SKIP {{ P }}.
Proof.
    unfold hoare_triple. intros P st st' H HP.
    inversion H; subst. assumption.
Qed.

Theorem hoare_seq: forall P Q R c1 c2,
    {{ Q }} c2 {{ R }} ->
    {{ P }} c1 {{ Q }} ->
    {{ P }} c1;;c2 {{ R }}.
Proof.
    intros P Q R c1 c2 H1 H2. unfold hoare_triple.
    intros st st' Heval HP.
    inversion Heval; subst.
    apply (H1 st'0 st'); try assumption.
    apply (H2 st st'0); assumption.
Qed.

Example hoare_asgn_examples_example3: forall a n,
    {{ fun st => aeval st a = n }}
    X ::=a;; SKIP
    {{ fun st => st X = n }}.
Proof.
    intros a n. eapply hoare_seq.
    Case "c2".
        apply hoare_skip.
    Case "c1".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assert_implies. intros st H. subst.
        unfold assn_sub. apply update_eq.
Qed.

Example hoare_asgn_examples_example4:
    {{ fun st => True }}
    X ::= ANum 1;; Y ::= ANum 2
    {{ fun st => (st X = 1 /\ st Y = 2) }}.
Proof.
    eapply hoare_seq.
    Case "c2".
        apply hoare_asgn.
    Case "c1".
        eapply hoare_consequence_pre.
        apply hoare_asgn.
        unfold assert_implies. unfold assn_sub. simpl.
        intros st HTrue. split; reflexivity.
Qed.

Definition swap_program: com :=
    Z ::= AId X;; X ::= AId Y;; Y ::= AId Z.

Theorem swap_exercise:
    {{ fun st => st X <= st Y }}
    swap_program
    {{ fun st => st Y <= st X }}.
Proof.
    eapply hoare_seq.
    Case "c2;;c3".
        eapply hoare_seq.
        apply hoare_asgn.
        apply hoare_asgn.
    Case "c1".
        eapply hoare_consequence_pre.
        apply hoare_asgn.
        unfold assert_implies, assn_sub. simpl.
        intros st H. compute. fold X Y. assumption.
Qed.

Definition bassn b : Assertion :=
    fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
    beval st b = true -> (bassn b) st.
Proof.
    intros b st H. unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
    beval st b = false -> ~ ((bassn b) st).
Proof.
    intros b st H. unfold not. intro contra.
    unfold bassn in contra. rewrite H in contra. inversion contra.
Qed.

Theorem hoare_if: forall P Q b c1 c2,
    {{ fun st => P st /\ bassn b st }} c1 {{ Q }} ->
    {{ fun st => P st /\ ~(bassn b st) }} c2 {{ Q }} ->
    {{ P }} (IFB b THEN c1 ELSE c2 FI) {{ Q }}.
Proof.
    intros P Q b c1 c2 Htrue Hfalse.
    unfold hoare_triple. intros st st' Heval HP.
    inversion Heval; subst.
    Case "b is true".
        eapply Htrue. 
            eassumption. 
            split. assumption. apply bexp_eval_true. assumption. 
    Case "b is false".
        eapply Hfalse.
            eassumption.
            split. assumption. apply bexp_eval_false. assumption.
Qed.

Example if_example:
    {{ fun st => True }}
    IFB (BEq (AId X) (ANum 0))
        THEN (Y ::= (ANum 2))
        ELSE (Y ::= APlus (AId X) (ANum 1))
    FI
    {{ fun st => st X <= st Y }}.
Proof.
    apply hoare_if.
    Case "Then".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold bassn, assn_sub, update, assert_implies.
        simpl. intros st [_ H].
        Check beq_nat_true.
        apply beq_nat_true in H. rewrite -> H. omega.
    Case "Else".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assn_sub, update, assert_implies.
        simpl. intros st _. omega.
Qed.

Theorem if_minus_plus:
    {{ fun st => True }}
    IFB (BLe (AId X) (AId Y))
        THEN (Z ::= AMinus (AId Y) (AId X))
        ELSE (Y ::= APlus (AId X) (AId Z))
    FI
    {{ fun st => st Y = st X + st Z }}.
Proof.
    apply hoare_if.
    Case "Then".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assert_implies, bassn, assn_sub, update.
        simpl. intros st [_ H]. apply ble_nat_true in H.
        inversion H; omega.
    Case "False".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assert_implies, assn_sub, update. simpl.
        intros st _. omega.
Qed.

Module If1.

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com
| CIf1 : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
    | Case_aux c "IFB" | Case_aux c "WHILE" | Case_aux c "CIF1" ].

Notation "'SKIP'" := CSkip.
Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
    (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" :=
    (CIf1 b c) (at level 80, right associativity).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st : state, SKIP / st || st
| E_Ass : forall (st : state) (a : aexp) (n : nat) (X : id),
        aeval st a = n -> (X ::= a) / st || update st X n
| E_Seq: forall (c1 c2 : com) (st st' st'' : state),
        c1 / st || st' -> c2 / st' || st'' -> (c1;; c2) / st || st''
| E_IfTrue : forall (st st' : state) (b : bexp) (c1 c2 : com),
        beval st b = true ->
        c1 / st || st' -> (IFB b THEN c1 ELSE c2 FI) / st || st'
| E_IfFalse : forall (st st' : state) (b : bexp) (c1 c2 : com),
        beval st b = false ->
        c2 / st || st' -> (IFB b THEN c1 ELSE c2 FI) / st || st'
| E_WhileEnd : forall (b : bexp) (st : state) (c : com),
        beval st b = false -> (WHILE b DO c END) / st || st
| E_WhileLoop : forall (b : bexp) (st st' st'' : state) (c : com),
        beval st b = true ->
        c / st || st' -> 
        (WHILE b DO c END) / st' || st'' ->
        (WHILE b DO c END) / st || st''
| E_If1True : forall (b : bexp) (st st' : state) (c : com),
        beval st b = true ->
        c / st || st' -> (IF1 b THEN c FI) / st || st'
| E_If1False : forall (b : bexp) (st : state) (c : com),
        beval st b = false -> (IF1 b THEN c FI) / st || st

where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
    | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
    | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
    | Case_aux c "E_If1True" | Case_aux c "E_If1False" ].

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
    forall st st',
    c / st || st' ->
    P st ->
    Q st'.

Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q)
    (at level 90, c at next level) : hoare_spec_scope.

Theorem hoare_if1: forall P Q b c,
    {{ fun st => P st /\ bassn b st }} c {{ Q }} ->
    {{ fun st => P st /\ ~(bassn b st) }} SKIP {{ Q }} ->
    {{ P }} (IF1 b THEN c FI) {{ Q }}.
Proof.
    intros P Q b c Htrue Hfalse. unfold hoare_triple.
    intros st st' Heval HP.
    inversion Heval; subst.
    Case "b is true".
        eapply Htrue. eassumption.
        split. assumption. apply bexp_eval_true. assumption.
    Case "b is false".
        unfold hoare_triple in Hfalse.
        eapply Hfalse. apply (E_Skip st').
        split. assumption. apply bexp_eval_false. assumption. 
Qed.

Theorem hoare_consequence_pre: forall (P P' Q : Assertion) c,
    {{ P' }} c {{ Q }} ->
    P ->> P' ->
    {{ P }} c {{ Q }}.
Proof.
    intros P P' Q c Hhoare Himp. unfold hoare_triple.
    intros st st' Hc HP. apply (Hhoare st st').
    assumption.
    apply Himp. assumption.
Qed.

Theorem hoare_asgn: forall Q X a,
    {{ Q [X |-> a] }} (X ::= a) {{ Q }}.
Proof.
    intros Q X a. unfold hoare_triple.
    intros st st' Heval HQ'.
    inversion Heval. subst.
    unfold assn_sub in HQ'. assumption.
Qed.

Theorem hoare_skip: forall P,
    {{ P }} SKIP {{ P }}.
Proof.
    unfold hoare_triple. intros P st st' H HP.
    inversion H; subst. assumption.
Qed.

Lemma hoare_if1_good:
    {{ fun st => st X + st Y = st Z }}
    IF1 BNot (BEq (AId Y) (ANum 0)) THEN
      X ::= APlus (AId X) (AId Y)
    FI
    {{ fun st => st X = st Z }}.
Proof.
    apply hoare_if1.
    Case "b is true".
        eapply hoare_consequence_pre. apply hoare_asgn.
        unfold assert_implies, bassn, assn_sub, update.
        simpl. intros st [H1 H2]. assumption.
   Case "b is false".
        eapply hoare_consequence_pre. apply hoare_skip.
        unfold not, bassn, assert_implies.
        simpl. intros st [H1 H2].
        remember (beq_nat (st Y) 0) as HY.
        destruct HY.
        SCase "st Y = 0". (* true *)
            symmetry in HeqHY. apply beq_nat_true in HeqHY.
            rewrite HeqHY in H1. rewrite <- H1. omega.
        SCase "st Y <> 0". (* contradiction *)
            simpl in H2. 
            apply ex_falso_quodlibet. apply H2. reflexivity.
Qed.

End If1.

Lemma hoare_while: forall P b c,
    {{ fun st => P st /\ bassn b st }} c {{ P }} ->
    {{ P }} WHILE b DO c END {{ fun st => P st /\ ~ (bassn b st) }}.
Proof.
    intros P b c. unfold hoare_triple. intros Hhoare st st' He HP.
    remember (WHILE b DO c END) as wcom eqn:Heqwcom.
    ceval_cases (induction He) Case;
        try (inversion Heqwcom); subst; clear Heqwcom.
    Case "E_WhileEnd".
        split. assumption. apply bexp_eval_false. assumption.
    Case "E_WhileLoop".
        apply IHHe2. reflexivity.
        eapply Hhoare. eassumption.
        split. assumption. apply bexp_eval_true. assumption.
Qed.

Example while_example:
    {{ fun st => st X <= 3 }}
    WHILE (BLe (AId X) (ANum 2))
    DO X ::= APlus (AId X) (ANum 1) END
    {{ fun st => st X = 3 }}.
Proof.
    eapply hoare_consequence_post.
    apply hoare_while.
    eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold bassn, assn_sub, assert_implies, update. simpl.
        intros st [H1 H2]. apply ble_nat_true in H2. omega.
    unfold bassn, assn_sub, assert_implies. intros st [Hle Hb].
        simpl in Hb. destruct (ble_nat (st X) 2) eqn:Heqle.
        apply ex_falso_quodlibet. apply Hb. reflexivity.
        apply ble_nat_false in Heqle. omega.
Qed.

Theorem always_loop_hoare: forall P Q,
    {{ P }} WHILE BTrue DO SKIP END {{ Q }}.
Proof.
    intros P Q.
    apply hoare_consequence_pre with (P' := fun st : state => True).
    eapply hoare_consequence_post.
    apply hoare_while.
    Case "Loop body preserves invariant".
        apply hoare_post_true. intros st. apply I.
    Case "Loop invariant and negated guard imply postcondition".
        simpl. intros st [Hinv Hguard].
        apply ex_falso_quodlibet. apply Hguard.
        unfold bassn. simpl. reflexivity.
    Case "Precondition implies invariont".
        unfold assert_implies. intros st H. constructor.
Qed.


