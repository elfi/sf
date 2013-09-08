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

Tactic Notation "simpl_and_try" tactic(c) :=
    simpl;
    try c.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ANum" | Case_aux c "APlus"
    | Case_aux c "AMin" | Case_aux c "AMult" ].

Theorem optimize_0plus_sound''': forall a,
    aeval (optimize_0plus a) = aeval a.
Proof.
    intro a.
    aexp_cases (induction a) Case;
        try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
        try reflexivity.
    Case "APlus".
        aexp_cases (destruct a1) SCase;
            try (simpl; simpl in IHa1;
                 rewrite IHa1; rewrite IHa2; reflexivity).
        SCase "ANum". destruct n;
            simpl; rewrite IHa2; reflexivity.
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | _ => b
    end.

Theorem optimize_0plus_b_sound : forall b,
    beval (optimize_0plus_b b) = beval b.
Proof.
    intro b.
    induction b; 
    (* cases not involving aexp *)
    try (simpl; reflexivity);
    (* cases with aexp *)
    try (simpl;
         rewrite -> optimize_0plus_sound;
         rewrite -> optimize_0plus_sound; reflexivity).
Qed.

Fixpoint optimizer (b : bexp) : bexp :=
    match b with
    | BAnd BTrue b2 => b2
    | BAnd BFalse b2 => BFalse
    | _ => b
    end.

Theorem optimizer_sound: forall b,
    beval (optimizer b) = beval b.
Proof.
    intro b.
    induction b; 
    (* cases without BAnd *)
    try (simpl; reflexivity);
    (* BAnd opt. at the first argument *)
    try (destruct b1; simpl; reflexivity).
Qed.

Example silly_presburger_example: forall m n o p,
    m + n <= n + o /\ o + 3 = p + 3 ->
    m <= p.
Proof.
    intros. omega.
Qed.

Module aevalR_first_try.

Inductive aevalR: aexp -> nat -> Prop :=
| E_ANum : forall (n:nat), aevalR (ANum n) n
| E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
        aevalR e1 n1 ->
        aevalR e2 n2 ->
        aevalR (AMult e1 e2) (n1 * n2).

Notation "e '||' n" := (aeval e n) : type_scope.

End aevalR_first_try.

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n:nat), (ANum n) || n
| E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
        (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
| E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
        (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
| E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
        (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)
                
where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "E_ANum"
    | Case_aux c "E_APlus"
    | Case_aux c "E_AMinus"
    | Case_aux c "E_AMult" ].

Theorem aeval_iff_aevalR : forall a n,
    (a || n) <-> aeval a = n.
Proof.
    split.
    Case "->".
        intro H.
        (* start with induction, prefix all goals with SCase and
           simpl all goals *)
        aevalR_cases (induction H) SCase; simpl.
        SCase "E_ANum". (* in case this does not match already
                        inserted SCase we get at error - it
                        helps us to keep track within automation *)
            reflexivity.
        SCase "E_APlus".
            rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
        SCase "E_AMinus".
            rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
        SCase "E_AMult".
            rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    Case "<-".
        generalize dependent n.
        aexp_cases (induction a) SCase; simpl; intros; subst.
        SCase "ANum".
            apply E_ANum.
        SCase "APlus".
            apply E_APlus.
              apply IHa1. reflexivity.
              apply IHa2. reflexivity.
        SCase "AMin".
            apply E_AMinus.
              apply IHa1. reflexivity.
              apply IHa2. reflexivity.
        SCase "AMult".
            apply E_AMult.
              apply IHa1. reflexivity.
              apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR': forall a n,
    (a || n) <-> aeval a = n.
Proof.
    split.
    Case "->".
        intro H; induction H; subst; reflexivity.
    Case "<-".
        generalize dependent n.
        induction a; simpl; intros; subst; constructor;
            try apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR: bexp -> bool -> Prop :=
| E_BTrue : bevalR BTrue true
| E_BFalse : bevalR BFalse false
| E_BEq : forall (e1 e2 : aexp) (n1 n2 : nat),
        e1 || n1 ->
        e2 || n2 ->
        bevalR (BEq e1 e2) (beq_nat n1 n2)
| E_BLe : forall (e1 e2 : aexp) (n1 n2 : nat),
        e1 || n1 ->
        e2 || n2 ->
        bevalR (BLe e1 e2) (ble_nat n1 n2)
| E_BNot : forall (e : bexp) (b : bool),
        bevalR e b ->
        bevalR (BNot e) (negb b)
| E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
        bevalR e1 b1 ->
        bevalR e2 b2 ->
        bevalR (BAnd e1 e2) (andb b1 b2).

Theorem beval_iff_bevalR : forall e b,
    bevalR e b <-> beval e = b.
Proof.
    split.
    Case "->".
        intro H; induction H; simpl;
        try (apply aeval_iff_aevalR in H);
        try (apply aeval_iff_aevalR in H0);
        subst; reflexivity.
    Case "<-".
        generalize dependent b.
        induction e; simpl; intros; subst; constructor;
        try (apply aeval_iff_aevalR; reflexivity);
        try (apply IHe;  reflexivity);
        try (apply IHe1; reflexivity);
        try (apply IHe2; reflexivity).
Qed.

Module aevalR_division.

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| ADiv : aexp -> aexp -> aexp.

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n:nat), (ANum n) || n
| E_APlus : forall (a1 a2 : aexp) (n1 n2 : nat),
        (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
| E_AMinus : forall (a1 a2 : aexp) (n1 n2 : nat),
        (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
| E_AMult : forall (a1 a2 : aexp) (n1 n2 : nat),
        (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)
| E_ADiv : forall (a1 a2 : aexp) (n1 n2 n3 : nat),
        (a1 || n1) -> (a2 || n2) -> (mult n2 n3 = n1) ->
                (ADiv a1 a2) || n3

where "a '||' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.
Inductive aexp : Type :=
| AAny : aexp
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive aevalR : aexp -> nat -> Prop :=
| E_Any : forall (n:nat), AAny || n
| E_ANum : forall (n:nat), (ANum n) || n
| E_APlus : forall (a1 a2 : aexp) (n1 n2 : nat),
        (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
| E_AMinus : forall (a1 a2 : aexp) (n1 n2 : nat),
        (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
| E_AMult : forall (a1 a2 : aexp) (n1 n2 : nat),
        (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)

where "a '||' n" := (aevalR a n) : type_scope.
End aevalR_extended.

Module Id.

Inductive id : Type :=
    Id : nat -> id.

Theorem eq_id_dec : forall id1 id2 : id,
    {id1 = id2} + {id1 <> id2}.
Proof.
     intros id1 id2.
     destruct id1 as [n1]. destruct id2 as [n2].
     destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
     Case "n1 = n2".
         left. rewrite Heq. reflexivity.
     Case "n1 <> n2".
         right. intro contra. inversion contra. apply Hneq.
         apply H0.
Defined.

Lemma eq_id : forall (T:Type) (x:id) (p q:T),
    (if eq_id_dec x x then p else q) = p.
Proof.
    intros. destruct (eq_id_dec x x).
    Case "x = x".
        reflexivity.
    Case "x <>x (impossible)".
        apply ex_falso_quodlibet; apply n; reflexivity.
Qed.

Lemma neq_id : forall (T:Type) (x y : id) (p q:T),
    x <> y ->
    (if eq_id_dec x y then p else q) = q.
Proof.
    intros. destruct (eq_id_dec x y).
    Case "x = y (contradicting hypothesis)".
        apply ex_falso_quodlibet; apply H; apply e.
    Case "x <> y".
        reflexivity.
Qed.

Definition state := id -> nat.

(* empty_state and update are the only two state 'builders' *)

Definition empty_state : state :=
    fun _:id => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
    fun x' => if eq_id_dec x x' then n else st x'.

Theorem update_eq : forall n x st,
    (update st x n) x = n.
Proof.
    intros. unfold update. destruct (eq_id_dec x x).
    Case "x = x".
        reflexivity.
    Case "x <> x (impossible)".
        apply ex_falso_quodlibet; apply n0; reflexivity.
Qed.

Theorem update_neq : forall x2 x1 n st,
    x2 <> x1 ->
    (update st x2 n) x1 = (st x1).
Proof.
    intros. unfold update. destruct (eq_id_dec x2 x1).
    Case "x2 = x1 (contradicts hypothesis)".
        apply ex_falso_quodlibet; apply H; apply e.
    Case "x2 <> x1".
        reflexivity.
Qed.

Theorem update_example : forall (n:nat),
    (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
    intros. unfold update. unfold empty_state.
    apply neq_id.
    intro contra. inversion contra.
Qed.

Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
    (update (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
    intros. unfold update. destruct (eq_id_dec x2 x1).
    Case "x2 = x1". reflexivity.
    Case "x2 <> x1". reflexivity.
Qed.

Theorem update_same : forall n1 x1 x2 (st : state),
    st x1 = n1 ->
    (update st x1 n1) x2 = st x2.
Proof.
    intros. unfold update. destruct (eq_id_dec x1 x2).
    Case "x1 = x2". subst; reflexivity.
    Case "x1 <> x2". reflexivity.
Qed.

Theorem update_permute : forall n1 n2 x1 x2 x3 st,
    x2 <> x1 ->
        (update (update st x2 n1) x1 n2) x3
      = (update (update st x1 n2) x2 n1) x3.
Proof.
    intros. unfold update. destruct (eq_id_dec x1 x3).
    Case "x1 = x3". subst. rewrite neq_id. reflexivity. apply H.
    Case "x1 <> x3". reflexivity.
Qed.

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : id -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
    | Case_aux c "AMinus" | Case_aux c "AMult" ].

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "BTrue" | Case_aux c "BFalse"
    | Case_aux c "BEq" | Case_aux c "BLe"
    | Case_aux c "BNot" | Case_aux c "BAnd" ].

Fixpoint aeval (st : state) (a : aexp) : nat :=
    match a with
    | ANum n        => n
    | AId x         => st x
    | APlus a1 a2   => (aeval st a1) + (aeval st a2)
    | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
    | AMult a1 a2   => (aeval st a1) * (aeval st a2)
    end.

Fixpoint beval (st : state) (b : bexp) : bool :=
    match b with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
    | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
    | BNot b1     => negb (beval st b1)
    | BAnd b1 b2  => andb (beval st b1) (beval st b2)
    end.

Example aexp1 :
    aeval (update empty_state X 5)
          (APlus (ANum 3) (AMult (AId X) (ANum 2)))
    = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (update empty_state X 5)
          (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
    = true.
Proof. reflexivity. Qed.
