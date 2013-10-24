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


