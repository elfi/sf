Require Export MoreProp.

Inductive and (P Q : Prop) : Prop :=
    conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.

Theorem and_example:
    (beautiful 0) /\ (beautiful 3).
Proof.
    apply conj.
    apply b_0.
    apply b_3.
Qed.

Print and_example.

Theorem and_example':
    (ev 0) /\ (ev 4).
Proof.
    split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.
Qed.

Theorem proj1: forall P Q : Prop,
    P /\ Q -> P.
Proof.
    intros P Q H.
    inversion H as [HP HQ].
    apply HP.
Qed.

Theorem proj2: forall P Q : Prop,
    P /\ Q -> Q.
Proof.
    intros P Q H.
    inversion H as [HP HQ].
    apply HQ.
Qed.

Theorem and_commut: forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
    intros P Q H. inversion H as [HP HQ].
    split. apply HQ. apply HP.
Qed.

Print and_commut.

Theorem and_assoc: forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
    intros P Q R H.
    inversion H as [HP [HQ HR]].
    split. split. apply HP. apply HQ. apply HR.
Qed.

Theorem even__ev: forall n:nat,
    (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
    intros n. induction n as [| n'].
    Case "O".
        split.
        intro H. apply ev_0.
        intro H. inversion H.  
    Case "S n'".
        split. apply IHn'. 
        intro H. apply ev_SS. apply IHn'. inversion H.
        unfold even. apply H1.
Qed.

Definition conj_fact: forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
    fun (P Q R : Prop) (EPQ : P /\ Q) (EQR : Q /\ R) =>
        match EPQ with
        | conj p q => match EQR with
                      | conj q' r => conj P R p r
                      end
        end.

Check conj_fact.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

Theorem iff_implies: forall P Q : Prop,
    (P <-> Q) -> P -> Q.
Proof.
    intros P Q H. inversion H as [ PimplQ QimplP ].
    apply PimplQ.
Qed.

Theorem iff_sym: forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
    intros P Q H. inversion H as [ PimplQ QimplP ].
    split. apply QimplP. apply PimplQ.
Qed.

Theorem iff_refl: forall P : Prop,
    P <-> P.
Proof.
    intro P. split. intro H. apply H. intro H. apply H.
Qed.

Theorem iff_trans: forall P Q R : Prop,
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
    intros P Q R EPQ EQR. inversion EPQ. inversion EQR. split.
    intro HP. apply H1. apply H. apply HP.
    intro HR. apply H0. apply H2. apply HR.
Qed.

Definition beautiful_iff_gorgeous:
    forall n, beautiful n <-> gorgeous n :=
    fun n => conj (beautiful n -> gorgeous n)
                  (gorgeous n -> beautiful n)
                  (beautiful__gorgeous n)
                  (gorgeous__beautiful n).

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.

Check or_intror.

Theorem or_commut: forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
    intros P Q EPoQ. inversion EPoQ as [EP | EQ].
    Case "left". apply or_intror. apply EP.
    Case "rigth". apply or_introl. apply EQ.
Qed.

Theorem or_commut': forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
    intros P Q EPoQ. inversion EPoQ as [ EP | EQ ].
    Case "left". right. apply EP.
    Case "right". left. apply EQ.
Qed.

Definition or_commut'':
    forall P Q : Prop, P \/ Q -> Q \/ P :=
    fun (P Q : Prop) (EPoQ : P \/ Q) =>
        match EPoQ with
        | or_introl p => or_intror Q P p
        | or_intror q => or_introl Q P q
        end.

Check or_commut''.

Theorem or_distributes_over_and_1: forall P Q R : Prop,
    P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R E. inversion E as [ EP | [ EQ ER] ].
    Case "left". split.
        SCase "left". left. apply EP.
        SCase "right". left. apply EP.
    Case "rigth". split.
        SCase "left". right. apply EQ.
        SCase "right". right. apply ER.
Qed.

Theorem or_distributes_over_and_2: forall P Q R : Prop,
    (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
    intros P Q R E. inversion E as [ [ EP | EQ ] [ EP' | ER ] ]. 
    Case "P P". left. apply EP.
    Case "P R". left. apply EP.
    Case "Q P". left. apply EP'.
    Case "Q R". right. split. apply EQ. apply ER.
Qed.

Theorem or_distributes_over_and: forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
    intros P Q R. split. 
    intro E. apply or_distributes_over_and_1. apply E.
    intro E. apply or_distributes_over_and_2. apply E.
Qed.


