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

