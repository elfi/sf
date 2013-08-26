Require Export SfLib.

Module AExp.

(* abstract syntax of arithmetic expressions *)
Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

(* abstract syntax of boolean expressions *)
Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

Example test_aeval1:
    aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | APlus (ANum 0) e2 => optimize_0plus e2
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.

Example test_optimize_0plus:
    optimize_0plus (APlus (ANum 2)
                          (APlus (ANum 0)
                                 (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
    aeval (optimize_0plus a) = aeval a.
Proof.
    intro a. induction a.
    Case "ANum". simpl. reflexivity.
    Case "APlus". destruct a1.
        SCase "a1 = ANum n". destruct n.
            SSCase "n = O". simpl. apply IHa2.
            SSCase "n = S ..". simpl. rewrite -> IHa2. reflexivity.
        SCase "a1 = APlus a1_1 a1_2". 
            simpl. simpl in IHa1. rewrite -> IHa1.
            rewrite IHa2. reflexivity.
        SCase "a1 = AMinus a1_1 a1_2".
            simpl. simpl in IHa1. rewrite -> IHa1.
            rewrite -> IHa2. reflexivity.
        SCase "a1 = AMult a1_1 a1_2".
            simpl. simpl in IHa1. rewrite -> IHa1.
            rewrite -> IHa2. reflexivity.
    Case "AMinus".
        simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
    Case "AMult".
        simpl. rewrite -> IHa1. rewrite -> IHa2. reflexivity.
Qed.

Theorem ev100: ev 100.
Proof.
    repeat (apply ev_SS).
    apply ev_0.
Qed.

Theorem ev100': ev 100.
Proof.
    repeat (apply ev_0).
    repeat (apply ev_SS). apply ev_0.
Qed.

Theorem silly1: forall ae, aeval ae = aeval ae.
Proof. try reflexivity. Qed.

Theorem silly2: forall (P : Prop), P -> P.
Proof.
    intros P HP.
    try reflexivity.
    apply HP.
Qed.

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
    intro n. destruct n.
    Case "n = O". simpl. reflexivity.
    Case "n = S ..". simpl. reflexivity.
Qed.

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
    intro n.
    destruct n; simpl; reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
    aeval (optimize_0plus a) = aeval a.
Proof.
    intro a.
    induction a;
        try (simpl; rewrite -> IHa1; rewrite -> IHa2; reflexivity ).
    (* remaining cases *)
    Case "ANum". reflexivity.
    Case "APlus".
        destruct a1;
            try (simpl; simpl in IHa1; rewrite -> IHa1;
                 rewrite -> IHa2; reflexivity).
        SCase "a1 = ANum n".
            destruct n; simpl; rewrite -> IHa2; reflexivity.
Qed.

Theorem optimize_0plus_sound'': forall a,
    aeval (optimize_0plus a) = aeval a.
Proof.
    intro a.
    induction a;
        (* most cases follow directly by the IH *)
        try (simpl; rewrite -> IHa1; rewrite -> IHa2; reflexivity);
        (* or are immediate by definition *)
        try reflexivity.
    (* the interesting case is when a = APlus a1 a2 *)
    Case "APlus".
        destruct a1; try (simpl; simpl in IHa1; rewrite -> IHa1;
                          rewrite -> IHa2; reflexivity).
        SCase "a1 = ANum n".
            destruct n; simpl; rewrite -> IHa2; reflexivity.
Qed.
