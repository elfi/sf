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

Inductive com : Type :=
| CSkip : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;" 
    | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" := CSkip.
Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
    (CIf b c1 c2) (at level 80, right associativity).

Definition fact_in_coq : com :=
    Z ::= AId X;;
    Y ::= ANum 1;;
    WHILE BNot (BEq (AId Z) (ANum 0)) DO
        Y ::= AMult (AId Y) (AId Z);;
        Z ::= AMinus (AId Z) (ANum 1)
    END.

Definition plus2 : com :=
    X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
    Z ::= (AMult (AId X) (AId Y)).

Definition substract_slowly_body : com :=
    Z ::= AMinus (AId Z) (ANum 1);;
    X ::= AMinus (AId X) (ANum 1).

(* Loops *)

Definition substract_slowly : com :=
    WHILE BNot (BEq (AId X) (ANum 0)) DO
        substract_slowly_body
    END.

Definition substract_3_from_5_slowly : com :=
    X ::= ANum 3;;
    Z ::= ANum 5;;
    substract_slowly.

(* Infinite loop *)

Definition loop : com :=
    WHILE BTrue DO
        SKIP
    END.

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
    match c with
    | SKIP => st
    | x ::= a1 => update st x (aeval st a1)
    | c1 ;; c2 => let st' := ceval_fun_no_while st c1 in
                  ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
            if (beval st b) then ceval_fun_no_while st c1
            else ceval_fun_no_while st c2
    | WHILE b DO c END => st (* bogus *)
    end.

Reserved Notation "c1 '/' st '||' st'" 
    (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st, SKIP / st || st
| E_Ass  : forall st a1 n x,
        aeval st a1 = n ->
        (x ::= a1) / st || (update st x n)
| E_Seq  : forall c1 c2 st st' st'',
        c1 / st || st' ->
        c2 / st' || st'' ->
        (c1 ;; c2) / st || st''
| E_IfTrue : forall st st' b c1 c2,
        beval st b = true ->
        c1 / st || st' ->
        (IFB b THEN c1 ELSE c2 FI) / st || st'
| E_IfFalse : forall st st' b c1 c2,
        beval st b = false ->
        c2 / st || st' ->
        (IFB b THEN c1 ELSE c2 FI) / st || st'
| E_WhileEnd : forall b st c,
        beval st b = false ->
        (WHILE b DO c END) / st || st
| E_WhileLoop : forall b st st' st'' c,
        beval st b = true ->
        c / st || st' ->
        (WHILE b DO c END) / st' || st'' ->
        (WHILE b DO c END) / st || st''

where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic (first) ident(c) :=
    first;
    [ Case_aux c "E_Skip" | Case_aux c "E_Ass"
    | Case_aux c "E_Seq" | Case_aux c "E_IfTrue"
    | Case_aux c "E_IfFalse" | Case_aux c "E_WhileEnd"
    | Case_aux c "E_WhileLoop" ].

Example ceval_examle1:
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1) THEN Y ::= ANum 3
     ELSE Z ::= ANum 4
     FI) / empty_state || (update (update empty_state X 2) Z 4).
Proof.
    (* we must supply the intermediate step *)
    apply E_Seq with (update empty_state X 2).
    Case "assignment command".
        apply E_Ass. simpl. reflexivity.
    Case "if command".
        apply E_IfFalse.
        reflexivity.
        apply E_Ass. simpl. reflexivity.
Qed.

Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
    remember (update empty_state X 0) as st.
    apply E_Seq with st.
    Case "first assignment".
        subst. apply E_Ass. simpl. reflexivity.
    Case "second assignment".
        remember (update st Y 1) as st'.
        apply E_Seq with st'.
        subst. apply E_Ass. simpl. reflexivity.
        SCase "third assignment".
            subst. apply E_Ass. simpl. reflexivity.
Qed.

Definition pup_to_n : com :=
    Y ::= ANum 0;;
    WHILE (BLe (ANum 1) (AId X)) DO
        Y ::= APlus (AId Y) (AId X);;
        X ::= AMinus (AId X) (ANum 1)
    END.

Theorem pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
    unfold pup_to_n.
    apply E_Seq with (update (update empty_state X 2) Y 0).
    apply E_Ass. reflexivity.
    apply E_WhileLoop with 
      (update (update (update 
          (update empty_state X 2) Y 0) Y 2) X 1).
    simpl. reflexivity.
    apply E_Seq with 
      (update (update (update empty_state X 2) Y 0) Y 2).
    apply E_Ass. reflexivity.
    apply E_Ass. reflexivity.
    apply E_WhileLoop with 
      (update (update (update (update (update
          (update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
    simpl. reflexivity.
    apply E_Seq with
      (update (update (update 
          (update (update empty_state X 2) Y 0) Y 2) X 1) Y 3).
    apply E_Ass. reflexivity.
    apply E_Ass. reflexivity.
    apply E_WhileEnd. reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to false".
      reflexivity.
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to true".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st || st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply update_eq.  Qed.

Theorem XtimesYinZ_spec : forall st n1 n2 st',
  st X = n1 ->
  st Y = n2 ->
  XtimesYinZ / st || st' ->
  st' Z = n1 * n2.
Proof.
    intros st n1 n2 st' HX HY Heval.
    inversion Heval. subst. simpl. apply update_eq.
Qed.

Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
  induction contra; inversion Heqloopdef.
  rewrite H1 in H. inversion H.
  subst. apply IHcontra2. assumption.
Qed.

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ;; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

Inductive no_whilesR: com -> Prop :=
| nowh_skip : no_whilesR SKIP
| nowh_ass  : forall X aexp, no_whilesR (X ::= aexp)  
| nowh_seq  : forall c1 c2, 
    no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1 ;; c2)
| nowh_if   : forall b c1 c2, 
    no_whilesR c1 -> no_whilesR c2 ->
        no_whilesR (IFB b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
    split.
    Case "->".
        intro H. induction c.
        SCase "Skip". apply nowh_skip.
        SCase "Ass". apply nowh_ass.
        SCase "Seq c1 c2". apply nowh_seq.
            SSCase "c1". apply IHc1. inversion H.
                         unfold andb. unfold andb in H1.
                         destruct (no_whiles c1).
                         symmetry. assumption. reflexivity.
            SSCase "c2". apply IHc2. inversion H.
                         unfold andb. unfold andb in H1.
                         destruct (no_whiles c1).
                         reflexivity. inversion H1.
        SCase "If b c1 c2". apply nowh_if.
            SSCase "c1". apply IHc1. inversion H.
                         unfold andb. unfold andb in H1.
                         destruct (no_whiles c1).
                         symmetry. assumption. reflexivity.
            SSCase "c2". apply IHc2. inversion H.
                         unfold andb. unfold andb in H1.
                         destruct (no_whiles c1).
                         reflexivity. inversion H1.
        SCase "While b c". inversion H.
    Case "<-".
        intro H. induction c.
        SCase "Skip". reflexivity.
        SCase "Ass". reflexivity.
        SCase "Seq c1 c2". simpl. inversion H.
            unfold andb. destruct (no_whiles c1).
            apply IHc2. assumption.
            apply IHc1. assumption.
        SCase "If b c1 c2". simpl. inversion H.
            unfold andb. destruct (no_whiles c1).
            apply IHc2. assumption.
            apply IHc1. assumption.
        SCase "While b c". inversion H.
Qed.

Theorem no_whiles_terminating : forall c st,
    no_whilesR c -> exists st', c / st || st'.
Proof.
    induction c.
    Case "Skip". intros. exists st. apply E_Skip.
    Case "Ass". intros. exists (update st i (aeval st a)). 
        apply E_Ass. reflexivity.
    Case "Seq". intros. inversion H. subst.
        assert (exists st1, c1 / st || st1) as c1_evaluates_to_st1. 
        SCase "Proof of assert". apply IHc1. apply H2.
        inversion c1_evaluates_to_st1.
        assert (exists st', c2 / x || st') 
            as c2_evaluates_to_st'. 
        SCase "Proof of assert". apply IHc2. apply H3.
        inversion c2_evaluates_to_st'.
        exists x0. apply E_Seq with x.
        assumption. assumption.
    Case "If". intros. inversion H. subst.
        assert (exists st1, c1 / st || st1) as c1_evals.
        SCase "Proof of assert". apply IHc1. assumption.
        assert (exists st2, c2 / st || st2) as c2_evals.
        SCase "Proof of assert". apply IHc2. assumption.
        inversion c1_evals. inversion c2_evals.
        remember (beval st b) as bevalb.
        destruct bevalb.
        SCase "True". exists x. apply E_IfTrue.
            symmetry. assumption. assumption.
        SCase "False". exists x0. apply E_IfFalse.
            symmetry. assumption. assumption.
    Case "While". intros. inversion H.
Qed.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Fixpoint s_execute (st : state) (stack : list nat)
    (prog : list sinstr) : list nat :=
    match prog with
    | nil => stack
    | instr :: prog' => match instr with
        | SPush n => s_execute st (n :: stack) prog'
        | SLoad xId => s_execute st ((st xId) :: stack) prog'
        | SPlus => match stack with
            | n2 :: n1 :: stack' =>
                s_execute st ((n1+n2) :: stack') prog'
            | _ => stack
            end
        | SMinus => match stack with
            | n2 :: n1 :: stack' =>
                s_execute st ((n1-n2) :: stack') prog'
            | _ => stack
            end
        | SMult => match stack with
            | n2 :: n1 :: stack' =>
                s_execute st ((n1*n2) :: stack') prog'
            | _ => stack
            end
        end
    end.

Example s_execute1 :
    s_execute empty_state nil
        [SPush 5; SPush 3; SPush 1; SMinus]
    = [2; 5].
Proof. simpl. reflexivity. Qed.

Example s_execute2 :
    s_execute (update empty_state X 3) [3; 4]
        [SPush 4; SLoad X; SMult; SPlus]
    = [15; 4].
Proof. simpl. reflexivity. Qed.

Fixpoint s_compile (e : aexp) : list sinstr :=
    match e with
    | ANum n => [SPush n]
    | AId xId => [SLoad xId]
    | APlus e1 e2 =>  s_compile e1 ++ s_compile e2 ++ [SPlus]
    | AMinus e1 e2 => s_compile e1 ++ s_compile e2 ++ [SMinus]
    | AMult e1 e2 => s_compile e1 ++ s_compile e2 ++ [SMult]
    end.

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. simpl. reflexivity. Qed.

Theorem s_execute_split :
    forall (e : aexp) (st : state) (stack : list nat)
           (prog : list sinstr),
    s_execute st stack (s_compile e ++ prog)
  = s_execute st ((aeval st e) :: stack) prog.
Proof.
    induction e.
    Case "Anum". intros. simpl. reflexivity.
    Case "AId". intros. simpl. reflexivity.
    Case "APlus". intros. simpl. (* I need to group things to prog *)
      assert (  (s_compile e1 ++ s_compile e2 ++ [SPlus]) ++ prog 
              = (s_compile e1 ++ (s_compile e2 ++ [SPlus] ++ prog)))
               as Regrouping.
      SCase "Proof of assert".
          rewrite -> app_ass. rewrite -> app_ass. reflexivity.
      rewrite -> Regrouping.
      assert (  s_execute st stack
                  (s_compile e1 ++ s_compile e2 ++ [SPlus] ++ prog)
              = s_execute st (aeval st e1 :: stack) (s_compile e2
                                                      ++ [SPlus]
                                                      ++ prog))
             as Exec_step.
      SCase "Proof of assert".
          apply IHe1.
      rewrite -> Exec_step. simpl.
      assert (   s_execute st (aeval st e1 :: stack)
                   (s_compile e2 ++ SPlus :: prog)
               = s_execute st (aeval st e2 :: aeval st e1 :: stack)
                   ( SPlus :: prog))
             as Exec_step2.
      SCase "Proof of assert".
          apply IHe2.
      rewrite -> Exec_step2. simpl. reflexivity.
    Case "AMinus". intros. simpl.
      assert (  (s_compile e1 ++ s_compile e2 ++ [SMinus]) ++ prog 
              = (s_compile e1 ++ (s_compile e2 ++ [SMinus] ++ prog)))
               as Regrouping.
      SCase "Proof of assert".
          rewrite -> app_ass. rewrite -> app_ass. reflexivity.
      rewrite -> Regrouping.
      assert (  s_execute st stack
                  (s_compile e1 ++ s_compile e2 ++ [SMinus] ++ prog)
              = s_execute st (aeval st e1 :: stack) (s_compile e2
                                                      ++ [SMinus]
                                                      ++ prog))
             as Exec_step.
      SCase "Proof of assert".
          apply IHe1.
      rewrite -> Exec_step. simpl.
      assert (   s_execute st (aeval st e1 :: stack)
                   (s_compile e2 ++ SMinus :: prog)
               = s_execute st (aeval st e2 :: aeval st e1 :: stack)
                   ( SMinus :: prog))
             as Exec_step2.
      SCase "Proof of assert".
          apply IHe2.
      rewrite -> Exec_step2. simpl. reflexivity.
    Case "AMult". intros. simpl.
      assert (  (s_compile e1 ++ s_compile e2 ++ [SMult]) ++ prog 
              = (s_compile e1 ++ (s_compile e2 ++ [SMult] ++ prog)))
               as Regrouping.
      SCase "Proof of assert".
          rewrite -> app_ass. rewrite -> app_ass. reflexivity.
      rewrite -> Regrouping.
      assert (  s_execute st stack
                  (s_compile e1 ++ s_compile e2 ++ [SMult] ++ prog)
              = s_execute st (aeval st e1 :: stack) (s_compile e2
                                                      ++ [SMult]
                                                      ++ prog))
             as Exec_step.
      SCase "Proof of assert".
          apply IHe1.
      rewrite -> Exec_step. simpl.
      assert (   s_execute st (aeval st e1 :: stack)
                   (s_compile e2 ++ SMult :: prog)
               = s_execute st (aeval st e2 :: aeval st e1 :: stack)
                   ( SMult :: prog))
             as Exec_step2.
      SCase "Proof of assert".
          apply IHe2.
      rewrite -> Exec_step2. simpl. reflexivity.
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
    s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
    induction e;
    try reflexivity;  (* ANum, Aid *)
    try (simpl;       (* APlus, AMinus, AMult *)
         rewrite -> s_execute_split;
         rewrite -> s_execute_split;
         simpl; reflexivity).
Qed.

Module BreakImp.

Inductive com : Type :=
| CSkip : com
| CBreak : com
| CAss : id -> aexp -> com
| CSeq : com -> com -> com
| CIf : bexp -> com -> com -> com
| CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "SKIP" | Case_aux c "BREAK"
    | Case_aux c "::=" | Case_aux c ";" 
    | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" := CSkip.
Notation "'BREAK'" := CBreak.
Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "c1 ; c2" :=
    (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
    (CIf b c1 c2) (at level 80, right associativity).


Inductive status : Type :=
| SContinue : status
| SBreak : status.

Reserved Notation "c1 '/' st '||' s '/' st'"
            (at level 40, st, s at level 39).

Inductive ceval : com -> state -> status -> state -> Prop :=
| E_Skip : forall st, CSkip / st || SContinue / st
| E_Break : forall st, CBreak / st || SBreak / st
| E_Ass : forall st a n x,
    aeval st a = n ->
    (x ::= a) / st || SContinue / (update st x n)
| E_SeqContinue : forall c1 c2 st st' st'' status,
    c1 / st || SContinue / st' ->
    c2 / st' || status / st'' ->
    (c1 ; c2) / st || status / st''
| E_SeqBreak : forall c1 c2 st st',
    c1 / st || SBreak / st' ->
    (c1 ; c2) / st || SBreak / st'
| E_IfTrue : forall b c1 c2 st st' state,
    beval st b = true ->
    c1 / st || state / st' ->
    (IFB b THEN c1 ELSE c2 FI) / st || state / st'
| E_IfFalse : forall b c1 c2 st st' state,
    beval st b = false ->
    c2 / st || state / st' ->
    (IFB b THEN c1 ELSE c2 FI) / st || state / st'
| E_WhileEnd : forall b c st,
    beval st b = false ->
    (WHILE b DO c END) / st || SContinue / st
| E_WhileLoopContinue : forall b c st st' st'',
    beval st b = true ->
    c / st || SContinue / st' ->
    (WHILE b DO c END) / st' || SContinue / st'' ->
    (WHILE b DO c END) / st || SContinue / st''
| E_WhileLoopBreak : forall b c st st',
    beval st b = true ->
    c / st || SBreak / st' ->
    (WHILE b DO c END) / st || SContinue / st'

  where "c1 '/' st '||' s '/' st'" := (ceval c1 st s st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Break"
  | Case_aux c "E_Ass" | Case_aux c "E_SeqContinue"
  | Case_aux c "E_SeqBreak" | Case_aux c "E_IfTrue"
  | Case_aux c "E_IfFalse" | Case_aux c "E_WhileEnd"
  | Case_aux c "E_WhileLoopContinue" 
  | Case_aux c "E_WhileLoopBreak" ].

Theorem break_ignore : forall c st st' s,
     (BREAK; c) / st || s / st' ->
     st = st'.
Proof.
    intros. inversion H. subst.
    inversion H2. (* contradiction *)
    subst. inversion H5. reflexivity.
Qed.

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st || s / st' ->
  s = SContinue.
Proof.
    intros. inversion H; reflexivity.
Qed.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st || SBreak / st' ->
  (WHILE b DO c END) / st || SContinue / st'.
Proof.
    intros. apply E_WhileLoopBreak; assumption.
Qed. 

Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st || SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' || SBreak / st'.
Proof.
    intros. remember (WHILE b DO c END) as WhileLoop.
    (* most cases *)
    ceval_cases(induction H) Case;
       try (inversion HeqWhileLoop);
       try subst.
    Case "E_WhileEnd". rewrite H in H0. inversion H0.
    Case "E_WhileLoopContinue". apply IHceval2; assumption.
    Case "E_WhileLoopBreak". exists st. assumption. 
Qed.

Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
    c / st || s1 / st1 ->
    c / st || s2 / st2 ->
    st1 = st2 /\ s1 = s2.
Proof.
    split. generalize dependent st2. generalize dependent s2.
    (* state *)
    ceval_cases (induction H) Case;
      intros s2 st2 E2;
      try (inversion E2);
      try subst;
      try reflexivity.
Admitted.

(* TODO: short_circuit *)
