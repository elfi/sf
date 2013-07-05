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

Theorem andb_true__and: forall b c,
    andb b c = true -> b = true /\ c = true.
Proof.
    intros b c H. unfold andb in H. destruct b.
    Case "true". split. reflexivity. apply H.
    Case "false". split. inversion H. inversion H.
Qed.

Theorem and__andb_true: forall b c,
    b = true /\ c = true -> andb b c = true.
Proof.
    intros b c H. inversion H. rewrite -> H0. rewrite -> H1.
    reflexivity.
Qed.

Theorem andb_false: forall b c,
    andb b c = false -> b = false \/ c = false.
Proof.
    intros b c H. unfold andb in H. destruct b.
    Case "true". right. apply H.
    Case "false". left. apply H.
Qed.

Theorem orb_true: forall b c,
    orb b c = true -> b = true \/ c = true.
Proof.
    intros b c H. unfold orb in H. destruct b.
    Case "true". left. apply H.
    Case "false". right. apply H.
Qed.

Theorem orb_false: forall b c,
    orb b c = false -> b = false /\ c = false.
Proof.
    intros b c H. unfold orb in H. destruct b.
    Case "true". split. apply H. destruct c. apply H. reflexivity.
    Case "false". split. reflexivity. apply H.
Qed.

Inductive False: Prop := .

Theorem False_implies_nonsence:
    False -> 2 + 2 = 5.
Proof.
    intro falseH. inversion falseH.
Qed.

Theorem nonsense_implies_False:
    2 + 2 = 5 -> False.
Proof.
    intro falseH. inversion falseH.
Qed.

Theorem ex_falso_quodlibet: forall (P:Prop),
    False -> P.
Proof.
    intros P falseH. inversion falseH.
Qed.

Inductive True: Prop :=
    tt : True.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

Theorem not_False:
    ~ False.
Proof.
    unfold not. intro falseH. inversion falseH.
Qed.

Print not_False.

Theorem contradiction_implies_anything: forall P Q : Prop,
    (P /\ ~P) -> Q.
Proof.
    intros P Q H. inversion H. unfold not in H1.
    apply H1 in H0. inversion H0.
Qed.

Theorem double_neg: forall P : Prop,
    P -> ~~P.
Proof.
    intros P HP. unfold not. intro HPimplFalse.
    apply HPimplFalse. apply HP.

Qed.

Print double_neg.

(* double neg informal:
  P -> ~~P  rewrite as P -> (P -> FALSE) -> FALSE, then
  after using modus ponens on P and (P -> FALSE), we
  trivially conclude that FALSE -> FALSE is true. *)

Theorem contrapositive: forall P Q : Prop,
    (P -> Q) -> (~Q -> ~P).
Proof.
    intros P Q HPimplQ. unfold not. intros HQimplF EP.
    apply HQimplF. apply HPimplQ. apply EP.
Qed.

Theorem not_both_true_and_false: forall P : Prop,
    ~ (P /\ ~P).
Proof.
    intro P. unfold not. intro H. inversion H.
    apply H1 in H0. apply H0.
Qed.

(* not both true and false informal:
   ~ (P /\ ~P)  rewrite as (P and (P -> FAlSE)) -> FALSE, then
   it is just to split the and and use modus ponens on P and
   (P -> FALSE). Thus FALSE becomes a hypethesis and it is
   trivial to prove a FALSE goal. *)

Theorem five_not_even:
    ~ ev 5.
Proof.
    unfold not. intro Hev5. inversion Hev5. inversion H0.
    inversion H2.
Qed.

Theorem ev_not_ev_S: forall n,
    ev n -> ~ ev (S n).
Proof.
    intros n Hev_n. unfold not. intro Hev_Sn. induction Hev_n.
    inversion Hev_Sn. apply IHHev_n. inversion Hev_Sn.
    apply H0.
Qed.

Definition peirce := forall P Q : Prop,
    ((P->Q)->P)->P.

Definition classic := forall P : Prop,
    ~~P -> P.

Definition excluded_middle := forall P : Prop,
    P \/ ~P.

Definition de_morgan_not_and_not := forall P Q : Prop,
    ~(~P/\~Q) -> P\/Q.

Definition implies_to_or := forall P Q : Prop,
    (P->Q) -> (~P\/Q).

Theorem excluded_middle_to_classic': forall P : Prop,
   (P \/ ~P) -> (~~P -> P).
Proof.
    intros P H. unfold not. intro H1. inversion H.
    Case "P". apply H0.
    Case "~P". unfold not in H0. apply H1 in H0. inversion H0.
Qed.

Theorem excluded_middle_to_classic:
    excluded_middle -> classic.
Proof.
    unfold excluded_middle. unfold classic.
    intro exclMiddle. intro P. unfold not. intro classic.
    specialize exclMiddle with P. inversion exclMiddle.
    Case "P". apply H.
    Case "~P". unfold not in H. apply classic in H. inversion H.
Qed.

Theorem peirce_to_classic: 
    peirce -> classic.
Proof.
    unfold peirce. unfold classic. intro peirce. intro P. 
    unfold not. intro classic.
    assert (P_false: (P -> False) -> P).
       intro H. apply classic in H. inversion H.
    apply peirce in P_false. apply P_false.
Qed.

Notation "x <> y" := (~(x = y)) : type_scope.

Theorem not_false_then_true: forall b : bool,
    b <> false -> b = true.
Proof.
    intros b H. unfold not in H. destruct b.
    Case "true". reflexivity.
    Case "false". apply ex_falso_quodlibet. apply H. reflexivity.
Qed.

Theorem not_eq_beq_false: forall n n' : nat,
    n <> n' ->
    beq_nat n n' = false.
Proof.
    intros n. induction n. (* keep IHn general *)
    Case "n = O". intros n' H. destruct n'.
         SCase "n' = O". simpl. apply ex_falso_quodlibet.
                         apply H. reflexivity.
         SCase "n' = S ..". simpl. reflexivity.
    Case "n = S ..". intros n' H. destruct n'.
         SCase "n' = O". simpl. reflexivity.
         SCase "n' = S ..". simpl. apply IHn.
            unfold not. intro H2. unfold not in H.
            apply eq_remove_S in H2. apply H. apply H2. 
Qed.

Theorem beq_false_not_eq: forall n m,
    false = beq_nat n m -> n <> m.
Proof.
    intros n m. intro H. unfold not. intro H2.
    rewrite -> H2 in H. rewrite <- beq_nat_refl in H. inversion H.
Qed.

Inductive ex (X:Type) (P : X->Prop) : Prop :=
    ex_intro : forall (witness:X), P witness -> ex X P.

Definition some_nat_is_even : Prop :=
    ex nat ev.

Definition snie: some_nat_is_even :=
    ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

Print snie.

Notation "'exists' x , p" := (ex _ (fun x => p))
    (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
    (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1: exists n, n + (n * n) = 6.
Proof.
    Check ex.
    apply ex_intro with (witness:=2).
    simpl. reflexivity.
Qed.

Example exists_example_1': exists n, n + (n * n) = 6.
Proof.
    exists 2. (* exists binding_list, for single constructors *)
    reflexivity.
Qed.

Theorem exists_example_2: forall n,
    (exists m, n = 4 + m) ->
    (exists o, n = 2 + o).
Proof.
    intros n H. inversion H as [m Hm].
    exists (2 + m). apply Hm.
Qed.

(* english_exists:
   exist n:nat, such that its successor is beautiful *)

Definition p : ex nat (fun n => beautiful (S n)) :=
    ex_intro nat (fun n => beautiful (S n)) 2 b_3.

Print p.

Theorem dist_not_exists: forall (X:Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
    intros X P Hforall. unfold not. intro Hex.
    inversion Hex as [x Hx]. apply Hx. apply Hforall.
Qed.


