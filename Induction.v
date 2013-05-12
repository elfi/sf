Require Export Basics.
Require String. Open Scope string_scope.

Ltac move_to_top x :=
    match reverse goal with
    | H : _ |- _ => try move x after H
    end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
    let H := fresh in
    assert (x = v) as H by reflexivity;
    clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
    first [
      set (x := name); move_to_top x
    | assert_eq x name; move_to_top x
    | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
Tactic Notation "SSSSSSSSCase" constr(name) := Case_aux SSSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
    andb b c = true -> b = true.
Proof.
    intros b c H.
    destruct b.
    Case "b = true".
      reflexivity.
    Case "b = false".
      rewrite <- H.
      reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
    intros b c H. destruct c.
    Case "c = true".
      reflexivity.
    Case "c = false".
      rewrite <- H.
      destruct b.
      SCase "b = true".
        reflexivity.
      SCase "b = false".
        reflexivity.
Qed.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
    n * 0 = 0.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
    intros n m.  induction n as [| n'].
    Case "n = 0". simpl. reflexivity.
    Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
    intros n m. induction n as [| n'].
    Case "n = 0".
        simpl. rewrite -> plus_0_r. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
    intros n m p.  induction n as [| n'].
    Case "n = 0". simpl. reflexivity.
    Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.

Lemma double_plus : forall n:nat,
    double n = n + n.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
    intros n m.
    assert (H: 0 + n = n).
        Case "Proof of assertion".
        reflexivity.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert (H: n + m = m + n).
        Case "Proof of assertion".
        rewrite -> plus_comm. reflexivity.
    rewrite -> H. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p. rewrite -> plus_assoc.
    assert (H: n + m = m + n).
        Case "Proof of assertion".
        rewrite -> plus_comm. reflexivity.
    rewrite -> H. rewrite <- plus_assoc. reflexivity.
Qed.


Lemma mult_Sm_r : forall n m : nat,
    n * (S m) = n + n * m.
Proof.
    intros n m. induction n as [|n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. rewrite -> plus_swap. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
    m * n = n * m.
Proof.
    intros m n. induction m as [| m'].
    Case "m = 0".
        simpl. rewrite -> mult_0_r. reflexivity.
    Case "m = S m'".
        simpl. rewrite -> mult_Sm_r. rewrite -> IHm'. reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n:nat,
    evenb n = negb (evenb (S n)).
Proof.
    intro n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl (evenb (S (S n'))).
        rewrite -> IHn'. rewrite -> negb_involutive.
        reflexivity.
Qed.

Theorem ble_nat_refl : forall n:nat,  (* induction needed *)
    true = ble_nat n n.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0".
        reflexivity.
    Case "n = S n'".
        simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat, (* simpl suffices *)
    beq_nat 0 (S n) = false.
Proof.
    reflexivity.
Qed.

Theorem andb_false_r: forall b:bool, (* destruct will do *)
    andb b false = false.
Proof.
    intro b. destruct b.
    Case "b = true".
        reflexivity.
    Case "b = false".
        reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, (* induction *)
    ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
    intros n m p H. induction p as [| p'].
    Case "p = 0".
        simpl. rewrite -> H. reflexivity.
    Case "p = S p'".
        simpl. rewrite -> IHp'. reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat, (* simpl will do *)
    beq_nat (S n) 0 = false.
Proof.
    intro n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, (* simpl & rewrite will do *)
    1 * n = n.
Proof.
    intro n. simpl. rewrite -> plus_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool, (* destruct will do *)
    orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
    intros b c. destruct b. destruct c.
    Case "b = true, c = true".
        simpl. reflexivity.
    Case "b = true, c = false".
        simpl. reflexivity.
    Case "b = false".
        simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat, (* induction *)
    (n + m) * p = (n * p) + (m * p).
Proof.
    intros n m p. induction n as [| n'].
    Case "n = 0".
        reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat, (* induction *)
    n * (m * p) = (n * m) * p.
Proof.
    intros n m p. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r.
        reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat, (* induction *)
    true = beq_nat n n.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0".
        reflexivity.
    Case "n = S n'".
        simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
    n + (m + p) = m + (n + p).
Proof.
    intros n m p. rewrite -> plus_assoc. 
    replace (n + m) with (m + n).
    rewrite <- plus_assoc. reflexivity.
    rewrite -> plus_comm. reflexivity.
Qed.

Inductive bin : Type :=
| bzero : bin
| P : bin -> bin
| Q : bin -> bin.

Fixpoint IncBin  (n:bin) : bin :=
    match n with
    | bzero => Q bzero
    | P n' => Q n'
    | Q n' => P (IncBin n')
    end.

Fixpoint BinToUnary (n:bin) : nat :=
    match n with
    | bzero => O
    | P n' => let a:nat := BinToUnary n' in 2 * a
    | Q n' => let a:nat := BinToUnary n' in S (2 * a)
    end.

Theorem binary_commute : forall b:bin,
    BinToUnary (IncBin b) = S (BinToUnary b).
Proof.
    intro b. induction b as [| b1 | b2 ].
    Case "b = bzero".
         simpl. reflexivity. 
    Case "b = P b1".
        simpl. reflexivity.
    Case "b = Q b2".
        simpl. rewrite -> plus_0_r. rewrite -> plus_0_r.
        rewrite IHb2. rewrite <- plus_n_Sm. simpl. reflexivity. 
Qed.

Fixpoint UnaryToBin (n:nat) : bin :=
    match n with
    | O    => bzero
    | S n' => IncBin (UnaryToBin n')
    end.

Theorem BinUnaryOneSideInversion : forall n:nat,
    BinToUnary (UnaryToBin n) = n.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0".
        simpl. reflexivity.
    Case "n = S n'".
        simpl. rewrite -> binary_commute. rewrite -> IHn'.
        reflexivity.
Qed.

Fixpoint normalize_helper (b:bin) (stack:bin->bin) : bin :=
    match b with
    | bzero => bzero
    | Q b' => stack (Q (normalize_helper b' (fun x:bin => x)))
    | P b' => normalize_helper b' (fun x:bin => P (stack x))
    end.

Definition normalize (b:bin) : bin :=
    normalize_helper b (fun x:bin => x).

Eval simpl in (normalize_helper (P (Q (P (P (P bzero)))))
                                (fun x:bin => x)).

Theorem UnaryBinNormalize : forall b:bin,
    UnaryToBin (BinToUnary b) = normalize b.
Proof.
    intro b. induction b as [| b1 | b2].
    Case "b = bzero".
        simpl. reflexivity.
    Case "b = P b1".
        unfold normalize. simpl. rewrite -> plus_0_r.
Admitted. (* the stack seems to be a hard nut *)




