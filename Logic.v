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

Check ex_intro.

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

Theorem not_exists_dist:
    excluded_middle ->
    forall (X:Type) (P : X->Prop),
      ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
    unfold excluded_middle. intro H.
    intros X P. unfold not. intro H1. intro x.
    specialize H with (P x).
    inversion H as [ Px | NotPx ].
    Case "Px".
        apply Px.
    Case "NotPx".
        apply ex_falso_quodlibet. unfold not in NotPx.
        apply H1. exists x. apply NotPx.
Qed. 

Theorem dist_exists_or: forall (X:Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
    intros X P Q. split.
    Case "->".
        intro H. inversion H as [ x Px_or_Qx ].
        inversion Px_or_Qx as [ Px | Qx ].
        SCase "Px". left. exists x. apply Px.
        SCase "Qx". right. exists x. apply Qx.
    Case "<-".
        intro H. inversion H as [ ex_x_Px | ex_x_Qx ].
        SCase "ex_x_Px". inversion ex_x_Px as [ x Px ].
            exists x. left. apply Px.
        SCase "ex_x_Qx". inversion ex_x_Qx as [ x Qx ].
            exists x. right. apply Qx.
Qed.

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
    refl_equal: forall x, eq X x x.

Check refl_equal.

Notation "x = y" := (eq _ x y)
                    (at level 70, no associativity) : type_scope.

Lemma leibniz_equality: forall (X:Type) (x y : X),
    x = y -> forall P : X -> Prop, P x -> P y.
Proof.
    intros X x y. intro xy_equal. intro P. intro H.
    Check refl_equal.
    inversion xy_equal as [ a ].
    rewrite <- H1. apply H.
Qed.

Definition four: 2 + 2 = 1 + 3 :=
    refl_equal nat 4. (* it builds a type 4 = 4 and
                         2 + 2 = 1 + 3 is convertible to
                         4 = 4 *)

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[] :=
    fun (X:Set) (x:X) => refl_equal (list X) [x].

End MyEquality.

Lemma dist_and_or_eq_implies_and: forall P Q R,
    P /\ (Q \/ R) /\ Q = R -> P /\ Q.
Proof.
    intros P Q R. intro H. split.
    Case "P".
        inversion H as [ P_witness theRest ]. apply P_witness.
    Case "Q".
        inversion H as [ P_witness theRest ].
        inversion theRest as [ Q_or_R_witness Q_eq_R_witness ].
        inversion Q_or_R_witness as [ Q_witness | R_witness ].
        SCase "Q".
            apply Q_witness.
        SCase "R".
            rewrite -> Q_eq_R_witness. apply R_witness.
Qed.

Definition funny_prop1 :=
    forall n, forall (E : beautiful n), beautiful (n+3).

Check funny_prop1.
Print funny_prop1.

Definition funny_prop1' :=
    forall n, forall (_ : beautiful n), beautiful (n+3).

Print funny_prop1'.

Definition funny_prop1'' :=
    forall n, beautiful n -> beautiful (n+3).

Module LeModule.

Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1:
    3 <= 3.
Proof.
    apply le_n.
Qed.

Theorem test_le2:
    3 <= 6.
Proof.
    apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Theorem test_le3:
    ~ (2 <= 1).
Proof.
    unfold not. intro H. inversion H. inversion H2.
Qed.

End LeModule.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
    sq : forall n:nat, square_of n (n*n).

Inductive next_nat (n:nat) : nat -> Prop :=
    nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
| ne_1 : ev (S n) -> next_even n (S n)
| ne_2 : ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation (n m : nat) : Prop :=
    total_rel : total_relation n m.

Inductive empty_relation (n m : nat) : Prop := .

Check square_of.
Check total_relation.
Check next_nat.

Inductive R : nat -> nat -> nat -> Prop :=
| c1 : R 0 0 0
| c2 : forall m n o, R m n o -> R (S m) n (S o)
| c3 : forall m n o, R m n o -> R m (S n) (S o)
| c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
| c5 : forall m n o, R m n o -> R n m o.

Theorem R112 : R 1 1 2.
Proof.
    apply c3. apply c2. apply c1.
Qed.

Theorem R_fact : forall m n o : nat,
    R m n o <-> m + n = o.
Proof.
    intros m n o. split.
    Case "->".
        intro H. induction H.
        SCase "c1".
            reflexivity.
        SCase "c2".
            simpl. rewrite -> IHR. reflexivity.
        SCase "c3".
            rewrite <- plus_n_Sm. rewrite -> IHR. reflexivity.
        SCase "c4". 
            inversion IHR. rewrite <- plus_n_Sm in H1. 
            apply eq_add_S in H1. apply H1.
        SCase "c5".
            rewrite plus_comm. apply IHR.
    Case "<-".
        intro H. induction H. induction m as [| m']. 
        SCase "O".
            simpl. induction n as [| n'].
            apply c1. apply c3. apply IHn'.
        SCase "n = S n'".
            simpl. apply c2. apply IHm'.
Qed.

Theorem notR226 : ~ ( R 2 2 6).
Proof.
    unfold not. intro H. apply R_fact in H. inversion H.
Qed.

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| all_nil :   all X P []
| all_elem :  forall (x : X) (l : list X), 
                P x -> all X P l -> all X P (x :: l).  


Fixpoint forallb {X : Type} (test : X -> bool) (l: list X) : bool :=
    match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
    end.

Theorem forallb_spec : forall (X:Type) (test : X->bool) (l : list X),
    forallb test l = true <-> all X (fun x:X => test x = true) l.
Proof.
    intros X test l. split.
    Case "->".
        intro H. induction l as [ | x l'].
        SCase "O". apply all_nil.
        SCase "l = x :: l'". apply all_elem.
            simpl in H. remember (test x) as tx. destruct tx.
            reflexivity. inversion H.
            apply IHl'. inversion H. remember (test x) as tx.
            destruct tx. simpl. reflexivity. simpl. inversion H1.
    Case "<-".
        intro H. induction H as [ | x l' ].
        SCase "nil".
            simpl. reflexivity.   
        SCase "l = x :: l'".
            simpl. remember (test x) as tx. destruct tx.
            simpl. apply IHall. simpl. inversion H.
Qed.

Inductive in_order_merge (X : Type) :
    list X -> list X -> list X -> Prop :=
    | in_order_merge_nil : 
            in_order_merge X nil nil nil
    | in_order_merge_l1 :
            forall (x : X) (l1 l2 l3 : list X),
            in_order_merge X l1 l2 l3 ->
            in_order_merge X (x :: l1) l2 (x :: l3)
    | in_order_merge_l2 :
            forall (x : X) (l1 l2 l3 : list X),
            in_order_merge X l1 l2 l3 ->
            in_order_merge X l1 (x :: l2) (x :: l3).

Lemma eq_remove_cons : forall {X : Type} (x : X) (l1 l2 : list X),
    l1 = l2 -> (x :: l1) = (x :: l2).
Proof.
    intros X x l1 l2 H. destruct l1 as [| x' l1'].
    Case "l1 = nil". rewrite <- H. reflexivity.
    Case "l1 = x' :: l1'". rewrite -> H. reflexivity.
Qed.

Theorem filter_challenge : 
    forall (X : Type) (l1 l2 l3 : list X) (test : X -> bool),
    in_order_merge X l1 l2 l3 ->
    all X (fun x => test x = true) l1 ->
    all X (fun x => test x = false) l2 ->
    filter test l3 = l1.
Proof.
    intros X l1 l2 l3 test Hl3inOrder Hl1allTrue Hl2allFalse.
    induction Hl3inOrder.
    Case "in_order_merge_nil contructor".
        simpl. reflexivity.
    Case "in_order_merge_l1 costructor".
        simpl. inversion Hl1allTrue. rewrite -> H1.
        apply eq_remove_cons. apply IHHl3inOrder.
        apply H2. apply Hl2allFalse.
    Case "in_order_merge_l2 contructor".
        simpl. inversion Hl2allFalse. rewrite -> H1. 
        apply IHHl3inOrder.
        apply Hl1allTrue. apply H2.
Qed.

Inductive appears_in {X : Type} (a:X) : list X -> Prop :=
| ai_here : forall l, appears_in a (a :: l)
| ai_later : forall b l, appears_in a l -> appears_in a (b :: l).

Lemma appears_in_app: forall {X:Type} (xs ys : list X) (x:X),
    appears_in x (xs ++ ys) -> 
    appears_in x xs \/ appears_in x ys.
Proof.
    intros X xs. induction xs as [| x' xs' ].
    Case "xs = nil".
        simpl. intros ys x H. right. apply H.
    Case "xs = x' :: xs'".
        simpl. intro ys. destruct ys as [| y' ys' ].
        SCase "ys = nil". 
            rewrite -> app_nil_end.
            intros x H. left. apply H.
        SCase "ys = y' :: ys'".
            intros x H. inversion H.
            SSCase "ai_here contructor".
                left. apply ai_here.
            SSCase "ai_later constructor".
                apply IHxs' in H1. inversion H1.
                SSSCase "left of H1".
                    left. apply ai_later. apply H3.
                SSSCase "rigt of H1".
                    right. apply H3.
Qed.

Lemma app_appears_in: forall {X:Type} (xs ys : list X) (x:X),
    appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
    intros X xs. induction xs as [| x' xs' ].
    Case "xs = nil".
        intros ys x H. simpl. inversion H.
        SCase "left of H". inversion H0.
        SCase "right of H". apply H0.
    Case"xs = x' :: xs'".
        intros ys x H. inversion H.
        SCase "left of H".
            inversion H0.
            SSCase "ai_here constructor".
                apply ai_here.
            SSCase "ai_later constructor".
                simpl. apply ai_later. apply IHxs'.
                left. apply H2.
        SCase "right of H".
            simpl. apply ai_later. apply IHxs'. right. apply H0.
Qed.

Definition disjoint (X:Type) (l1 l2 : list X) : Prop :=
    (forall x : X, appears_in x l1 -> ~ (appears_in x l2)) /\ 
    (forall x : X, appears_in x l2 -> ~ (appears_in x l1)).

Inductive no_repeats (X : Type) : list X -> Prop :=
| no_reps_nil  : no_repeats X []
| no_reps_cons : forall (x : X) (l : list X),
        no_repeats X l ->
        ~ (appears_in x l) ->
        no_repeats X (x :: l).

Example test_no_repeats1: no_repeats nat [1,2,3,4].
Proof.
    (* deal with the goal itself *)
    apply no_reps_cons. apply no_reps_cons.
    apply no_reps_cons. apply no_reps_cons.
    apply no_reps_nil.
    (* deal with generated assumptions *)
    unfold not. intro H. inversion H.
    unfold not. intro H. inversion H. inversion H1.
    unfold not. intro H. inversion H. inversion H1. inversion H4.
    unfold not. intro H. inversion H. inversion H1. inversion H4. 
                         inversion H7.
Qed.

Example test_no_repeats2: ~ (no_repeats bool [true, true]).
Proof.
    unfold not. intro H.
    inversion H. unfold not in H3. apply H3.
    apply ai_here.
Qed.

Lemma not_appear_in: forall {X : Type} (x:X) (l1 l2 : list X),
    ~ (appears_in x (l1 ++ l2)) ->
    ~ (appears_in x l1) /\ ~ (appears_in x l2).
Proof.
    intros X x l1 l2. unfold not.
    intro H. split.
    Case "left".
        intro Happl1. apply H. apply app_appears_in. left.
        apply Happl1.
    Case "right".
        intro Happl2. apply H. apply app_appears_in. right.
        apply Happl2.
Qed.

Theorem no_repeats__disjoint: forall (X : Type) (l1 l2 : list X),
    no_repeats X (l1 ++ l2) -> disjoint X l1 l2.
Proof.
    intros X l1. induction l1 as [| x l1'].
    Case "l1 = nil".
        simpl. intros l2 H. unfold disjoint. split.
        SCase "left".
            intros x Happear. inversion Happear.
        SCase "right".
            intros x Happear. unfold not. intro Happear2.
            inversion Happear2.
    Case "l1 = x :: l1'".
        simpl. intros l2 H. unfold disjoint. split.
        SCase "left".
            intros x0 Happear. unfold not. intro Happear2.
            inversion H. 
            (* only no_reps_cons constructor possible *)
            apply IHl1' in H2. unfold disjoint in H2.
            inversion H2.
            (* only one case for splitting of and *)
            unfold not in H4. unfold not in H5.
            unfold not in H3. subst.
            apply H5 in Happear2. apply Happear2.
            inversion Happear. subst. 
            apply not_appear_in in H3. inversion H3.
            unfold not in H1. apply H1 in Happear2.
            inversion Happear2.
            apply H1.
        SCase "right".
            intros x0 Happear. unfold not. intro Happear2.
            inversion H. subst. unfold not in H3.
            apply IHl1' in H2. unfold disjoint in H2.
            inversion H2.
            unfold not in H0. unfold not in H1.
            apply H1 in Happear. apply Happear.
            inversion Happear2. subst.
            apply not_appear_in in H3. inversion H3.
            unfold not in H5. apply H5 in Happear.
            inversion Happear.
            apply H5.
Qed.

Theorem O_le_n: forall n,
    0 <= n.
Proof.
    intro n. induction n as [| n'].
    Case "n = O". apply le_n.
    Case "n = S n'". apply le_S. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
    n <= m -> S n <= S m.
Proof.
    intros n m H. induction H.
    Case "base". apply le_n.
    Case "inductive step". apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m: forall n m,
    S n <= S m -> n <= m.
Proof.
    intros n m. generalize dependent n. induction m as [| m'].
    Case "m = O".
        intros n H. inversion H. reflexivity. inversion H1.
    Case "m = S m'".
        intro n. destruct n as [| n'].
        SCase "n = O".
            intro H. apply O_le_n.
        SCase "n = S n'".
            intro H. inversion H. 
            SSCase "le_n constructor".
                apply le_n.
            SSCase "le_S constructor".
                apply IHm' in H1. apply le_S. apply H1.
Qed.

Theorem le_plus_l: forall a b,
    a <= a + b.
Proof.
    intros a b. induction b as [| b'].
    Case "b = O". rewrite -> plus_0_r. apply le_n.
    Case "b = S b'". rewrite <- plus_n_Sm. apply le_S. apply IHb'.
Qed.

Theorem plus_lt: forall n1 n2 m,
    n1 + n2 < m ->
    n1 < m /\ n2 < m.
Proof.
    unfold lt. intros n1 n2 m H. induction H.
    Case "le_n constructor". split.
        SCase "left".
            apply n_le_m__Sn_le_Sm. apply le_plus_l.
        SCase "right".
            apply n_le_m__Sn_le_Sm. rewrite -> plus_comm.
            apply le_plus_l.
    Case "le_S constructor". inversion IHle. split.
        SCase "left".
             apply le_S. apply H0.
        SCase "right".
             apply le_S. apply H1.
Qed.

Theorem lt_S : forall n m,
    n < m ->
    n < S m.
Proof.
    unfold lt. intros n m H. apply le_S. apply H.
Qed.

Theorem ble_nat_true: forall n m,
    ble_nat n m = true -> n <= m.
Proof.
    intro n. induction n as [| n'].
    Case "n = O". intros m H. apply O_le_n.
    Case "n = S n'". intro m. destruct m.
        intro H. inversion H.
        intro H. apply n_le_m__Sn_le_Sm. apply IHn'. 
        simpl in H. apply H.
Qed.

Theorem ble_nat_n_Sn_false: forall n m,
    ble_nat n (S m) = false ->
    ble_nat n m = false.
Proof.
    intro n. induction n as [| n'].
    Case "n = O". intro m. intro H. inversion H.
    Case "n = S n'". intro m. destruct m.
        intro H. simpl. reflexivity.
        intro H. simpl. apply IHn'. simpl in H. apply H.
Qed.

Theorem ble_nat_false: forall n m,
    ble_nat n m = false -> ~ (n <= m).
Proof.
    intro n. induction n as [| n'].
    Case "n = O". intros m H. simpl in H. inversion H.
    Case "n = S n'". intro m. destruct m.
        intro H. unfold not. intro H1. inversion H1.
        intro H. unfold not. intro H1.
        simpl in H. apply IHn' in H. unfold not in H.
        apply H. apply Sn_le_Sm__n_le_m in H1. apply H1.
Qed.

Check beq_false_not_eq.
Inductive nostutter: list nat -> Prop :=
| nostutter_nil : nostutter []
| nostutter_singleton : forall x, nostutter [x]
| nostutter_two_different : forall x y l,
        x <> y ->
        nostutter (y :: l) ->
        nostutter (x :: y :: l).

Example test_nostutter_1: nostutter [3, 1, 4, 1, 5, 6].
Proof. 
    (* try out first step *)
    apply nostutter_two_different.
    apply beq_false_not_eq.
    simpl. reflexivity.
    (* automate the rest alike *)
    repeat constructor; apply beq_false_not_eq; auto.
Qed.

Example test_nostutter_2: nostutter [].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_3: nostutter [5].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_4: not (nostutter [3, 1, 1, 4]).
Proof.
    intro.
    (* make a list of all hypothesis, 3 <> 1, 1 <> 1, ... *)
    repeat match goal with
        h: nostutter _ |- _ => inversion h; clear h; subst
    end.
    (* this one is contradictory *)
    contradiction H1; auto.
Qed.

Lemma app_length: forall {X:Type} (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
    intros X l1. induction l1 as [| x l1'].
    Case "l1 = nil". intro l2. simpl. reflexivity.
    Case "l1 = x :: l1'". intro l2. simpl. apply eq_remove_S.
        apply IHl1'.
Qed.

Lemma appears_in_app_split: forall {X:Type} (x:X) (l:list X),
    appears_in x l ->
    exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
    intros X x l. generalize dependent x.
    induction l as [| x' l'].
    Case "l = nil".
        intros x H. inversion H.
    Case "l = x' :: l'".
        intros x H. inversion H. 
        SCase "ai_here".
            exists []. exists l'. reflexivity.
        SCase "ai_later".
            apply IHl' in H1. inversion H1. inversion H3.
            exists (x' :: witness). simpl. exists witness0.
            rewrite <- H4. reflexivity.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
| repeats_this_one   : forall a l,
        appears_in a l -> repeats (a :: l)
| repeats_later : forall b l, repeats l -> repeats (b :: l).

Example test_repeats: repeats [ 1, 4, 3, 2, 4, 8 ].
Proof.
    apply repeats_later. apply repeats_this_one.
    apply ai_later. apply ai_later. apply ai_here.
Qed.

Lemma appear_in__remove_redundant:
    forall {X : Type} (a b : X) (l1 l2 : list X),
    excluded_middle ->
    a <> b ->
    appears_in a (l1 ++ (b :: l2)) ->
    appears_in a (l1 ++ l2).
Proof.
    intros X a b l1. induction l1 as [| x l1'].
    Case "l1 = nil".
        simpl. intros l2 HexcM Hadiffb H. inversion H.
        SCase "ai_here constructor".
            apply ex_falso_quodlibet. apply Hadiffb. apply H1.
        SCase "ai_later".
            apply H1. 
    Case "l1 = x :: l1'".
        simpl. intros l2 HexcM Hadiffb H.
        assert (Havsx:
            (a = x) \/ (a <> x)).
            (* Proof of assert *)
            apply HexcM.
        inversion Havsx.
        SCase "a = x".
            subst. apply ai_here.
        SCase "a <> x".
            apply ai_later. apply IHl1'.
            (* Goals generated by the inductive hypothesis
               ------------------------------------------- *)
            (* excluded middle subgoal *)
                apply HexcM.
            (* a <> b *)
                apply Hadiffb.
            (* appears_in *)
                inversion H.
                SSCase "ai_here". (* absurd as a <> x *)
                    apply ex_falso_quodlibet. apply H0. apply H2.
                SSCase "ai_later".
                    apply H2.
Qed.

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
    excluded_middle ->
    (forall x, appears_in x l1 -> appears_in x l2) ->
    length l2 < length l1 ->
    repeats l1.
Proof.
    intros X l1. induction l1 as [| x' l1'].
    Case "l1 = nil".
        intros l2 HexcM H Hlen. inversion Hlen.
    Case "l1 = x' :: l1'".
        intros l2 HexcM H Hlen.
        assert (Hrepeatsl1':
            (appears_in x' l1') \/ ~(appears_in x' l1')).
            (* Proof of assert *)
            apply HexcM.
        inversion Hrepeatsl1'. 
        SCase "x' appears in l1' again".
            apply repeats_this_one. apply H0.
        SCase "x' does not appear in l1' any more".
            apply repeats_later.
            assert (Hl2split:
                exists preList, exists postList,
                l2 = preList ++ (x' :: postList)).
                (* Proof of assert *) 
                apply appears_in_app_split.
                apply H. apply ai_here.
            inversion Hl2split. inversion H1. 
            (* this effectively removes x' form l2 *)
            apply (IHl1' (witness ++ witness0)).
            (* Goals generated from inductive hypothesis
               ----------------------------------------- *)
            (* excluded middle subgoal *)
                apply HexcM.
            (* propetry subgoal *)
                intros x'' Happrl1.
                assert (Hx'vsx'':
                    (x' = x'' \/ x' <> x'')).
                    (* Proof of assert *)
                    apply HexcM.
                inversion Hx'vsx''.
                SSCase "x' = x''".
                    (* but then it is absurd for x''
                       to appear in (witness ++ witness0) *)
                    apply ex_falso_quodlibet.
                    apply H0. subst. apply Happrl1.
                SSCase "x' <> x''".
                    assert (Hx''inl2:
                        appears_in x'' l2).
                        (* Proof of assert *)
                        apply H. apply ai_later.
                        apply Happrl1. subst.
                    (* Now we need to put Hx''inl2 to use *)
                    apply appear_in__remove_redundant in Hx''inl2.
                    apply Hx''inl2.
                    (* Goals generated by the remove_redundant lemma
                       --------------------------------------------- *)
                    (* excluded middle subgoal *)
                        apply HexcM.
                    (* x'' <> x' *)
                        unfold not. intro Htemp. symmetry in Htemp.
                        apply H3. apply Htemp.
            (* length subgoal *)
                rewrite -> app_length.
                subst. rewrite -> app_length in Hlen.
                simpl in Hlen. rewrite <- plus_n_Sm in Hlen. 
                unfold lt. unfold lt in Hlen.
                apply Sn_le_Sm__n_le_m in Hlen. apply Hlen.
Qed.


