Require Export Poly.

Theorem silly1: forall (n m o p : nat),
    n = m ->
    [n,o] = [n,p] ->
    [n,o] = [m,p].
Proof.
    intros n m o p eq1 eq2.
    rewrite <- eq1.
    apply eq2.
Qed.

Theorem silly2: forall (n m o p : nat),
    n = m ->
    (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
    [n,o] = [m,p].
Proof.
    intros n m o p eq1 eq2.
    apply eq2. apply eq1.
Qed.

Theorem silly2a: forall (n m : nat),
    (n,n) = (m,m) ->
    (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
    [n] = [m].
Proof.
    intros n m eq1 eq2.
    apply eq2. apply eq1.
Qed.

Theorem silly_ex:
    (forall n, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true ->
    oddb 4 = true.
Proof.
    intros eq1 eq2.
    apply eq1. apply eq2.
Qed.

Theorem silly3: forall (n : nat),
    true = beq_nat n 5 ->
    beq_nat (S (S n)) 7 = true.
Proof.
    intros n eq1.
    symmetry.
    apply eq1.
Qed.

Theorem rev_exercise1: forall (l l' : list nat),
    l = rev l' ->
    l' = rev l.
Proof.
    intros l l' eq1.
    SearchAbout rev.
    rewrite -> eq1.
    symmetry.
    apply rev_involutive.
Qed.

Theorem eq_add_S: forall (n m : nat),
    S n = S m ->
    n = m.
Proof.
    intros n m eq. inversion eq. reflexivity.
Qed.

Theorem silly4: forall (n m : nat),
    [n] = [m] ->
    n = m.
Proof.
    intros n m eq. inversion eq. reflexivity.
Qed.

Theorem silly5: forall (n m o : nat),
    [n,m] = [o,o] ->
    [n] = [m].
Proof.
    intros n m o eq. inversion eq. reflexivity.
Qed.

Example sillyex1: forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    y :: l = x :: j ->
    x = y.
Proof.
    intros X x y z l j eq1 eq2.
    inversion eq1. inversion eq2.
    symmetry. apply H0.
Qed.

Example silly6: forall (n : nat),
    S n = O ->
    2 + 2 = 5.
Proof.
    intros n eq.
    inversion eq.
Qed.

Theorem silly7: forall (n m : nat),
    false = true ->
    [n] = [m].
Proof.
    intros n m eq. inversion eq.
Qed.

Example sillyex2: forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    y :: l = z :: j ->
    x = z.
Proof.
    intros X x y z l j eq1 eq2.
    inversion eq1.
Qed.

Lemma eq_remove_S: forall n m,
    n = m -> S n = S m.
Proof.
    intros n m eq. rewrite -> eq. reflexivity.
Qed.

Theorem length_snoc': forall (X : Type) (v : X)
                             (l : list X) (n : nat),
    length l = n ->
    length (snoc l v) = S n.
Proof.
    intros X v l. induction l as [| x xs].
    Case "l = nil".
        intros n eq. simpl. rewrite <- eq. reflexivity.
    Case "l = x :: xs".
        intros n eq. simpl. destruct n as [| n'].
        SCase "n = 0". inversion eq.
        SCase "n = S n'". apply eq_remove_S. apply IHxs.
                          inversion eq. reflexivity.
Qed.

Theorem beq_nat_0_l: forall n,
    true = beq_nat 0 n -> 0 = n.
Proof.
    intros n eq. inversion eq. destruct n.
    reflexivity. inversion H0.
Qed.

Theorem beq_nat_0_r: forall n,
    true = beq_nat n 0 -> 0 = n.
Proof.
    intros n eq. apply beq_nat_0_l.
    SearchAbout beq_nat.
    destruct n. reflexivity.
    inversion eq.
Qed.

Theorem S_inj: forall (n m : nat) (b : bool),
    beq_nat (S n) (S m) = b ->
    beq_nat n m = b.
Proof.
    intros n m b H. simpl in H. apply H.
Qed.

Theorem silly3': forall (n : nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
    intros n eq H.
    symmetry in H. apply eq in H. symmetry in H. apply H.
Qed.

Theorem plus_n_n_injective: forall n m,
    n + n = m + m ->
    n = m.
Proof.
    intro n. induction n as [| n'].
    Case "n = O".
        simpl. intros m eq.
        destruct m.  reflexivity.  inversion eq.
    Case "n = S n'".
        simpl. intros m eq.
        destruct m.
        SCase "m = O".
            simpl in eq. inversion eq.
        SCase "m = S m'".
            rewrite <- plus_n_Sm in eq. symmetry in eq.
            rewrite <- plus_n_Sm in eq.
            simpl in eq.
            apply eq_add_S in eq. apply eq_add_S in eq.
            symmetry in eq. apply IHn' in eq.
            apply eq_remove_S. apply eq.
Qed.

Theorem double_injective': forall n m,
    double n = double m ->
    n = m.
Proof.
    intro n. induction n as [| n'].
    Case "n = O". simpl. intros m eq. destruct m.
        reflexivity. inversion eq.
    Case "n = S n'". simpl. intros m eq. destruct m.
        inversion eq. apply eq_remove_S. apply IHn'.
        simpl in eq. apply eq_add_S in eq.
        apply eq_add_S in eq. apply eq.
Qed.

Theorem beq_nat_eq: forall n m,
    true = beq_nat n m -> n = m.
Proof.
    intro n. induction n as [| n'].
    Case "n = O". intros m eq. destruct m.
        reflexivity. inversion eq. 
    Case "n = S n'". intros m eq. destruct m.
        inversion eq. apply eq_remove_S. apply IHn'.
        simpl in eq. apply eq.
Qed.

Theorem double_injective_take2: forall n m,
    double n = double m ->
    n = m.
Proof.
    intros n m.
    generalize dependent n.
    induction m as [| m'].
    Case "m = O". intros n eq. destruct n.
        reflexivity. inversion eq.
    Case "m = S m'". intros n eq. destruct n.
        inversion eq. apply eq_remove_S. apply IHm'.
        simpl in eq. apply eq_add_S in eq.
        apply eq_add_S in eq. apply eq.
Qed.

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
    length l = n ->
    index (S n) l = None.
Proof.
    intros n X l. generalize dependent n. induction l as [| x xs].
    Case "l = nil". intros n eq.
        simpl. reflexivity.
    Case "l = x :: xs". intros n eq. simpl. destruct n.    
        simpl in eq. inversion eq.
        apply IHxs. simpl in eq. apply eq_add_S in eq. apply eq.
Qed.

Theorem length_snoc''': forall (n : nat) (X : Type)
                               (v : X) (l : list X),
    length l = n ->
    length (snoc l v) = S n.
Proof.
    intros n X v l. generalize dependent n. induction l as [| x xs].
    Case "l = nil". intros n eq.
        simpl in eq. simpl. rewrite <- eq. reflexivity.
    Case "l = x xs". intros n eq. destruct n.
        inversion eq. simpl. apply eq_remove_S. apply IHxs.
        simpl in eq. apply eq_add_S in eq. apply eq.
Qed.

Theorem app_length_cons: forall (X : Type) (l1 l2 : list X)
                                (x : X) (n : nat),
    length (l1 ++ (x :: l2)) = n ->
    S (length (l1 ++ l2)) = n.
Proof.
    intros X l1 l2 x n. generalize dependent n. induction l1 as [| x' xs].
    Case "l1 = nil". simpl. intros n eq. apply eq.
    Case "l1 = x' :: xs". simpl. intros n eq. destruct n.
        inversion eq. apply eq_remove_S. apply IHxs. 
        inversion eq. reflexivity.
Qed.

Theorem app_length_cons': forall (X : Type) (l1 l2 : list X)
                                (x : X) (n : nat),
    length (l1 ++ l2) = n ->
    length (l1 ++ (x :: l2)) = S n.
Proof.
    intros X l1 l2 x n. generalize dependent n. induction l1 as [| x' xs].
    Case "l1 = nil". simpl. intros n eq. rewrite -> eq. reflexivity.
    Case "l1 = x' :: xs". simpl. intros n eq.
        apply eq_remove_S. destruct n.
        inversion eq. apply IHxs. apply eq_add_S in eq. apply eq.
Qed.


Theorem app_length_twice: forall (X : Type) (n : nat) (l : list X),
    length l = n ->
    length (l ++ l) = n + n.
Proof.
    intros X n l. generalize dependent n. induction l as [| x xs].
    Case "l = nil". intros n eq. inversion eq. simpl. reflexivity.
    Case "l = x :: xs". simpl. intros n eq. destruct n.
        inversion eq. apply eq_add_S in eq. simpl. apply eq_remove_S.
        rewrite <- plus_n_Sm. apply app_length_cons'.
        apply IHxs. apply eq.
Qed.

Definition sillyfun (n : nat) : bool :=
    if beq_nat n 3 then false
    else if beq_nat n 5 then false
    else false.

Theorem sillyfun_false: forall (n : nat),
    sillyfun n = false.
Proof.
    intro n. unfold sillyfun.
    destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
        SCase "beq_nat n 5 = true". reflexivity.
        SCase "beq_nat n 5 = false". reflexivity.
Qed.

Theorem override_shadow: forall {X:Type} x1 x2 k1 k2 (f:nat->X),
    (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
    intros X x1 x2 k1 k2 f. unfold override. destruct (beq_nat k1 k2).
    reflexivity. reflexivity.
Qed.

Lemma eq_cons: forall (X:Type) (x:X) (l1 l2 : list X),
    l1 = l2 ->
    x :: l1 = x :: l2.
Proof.
    intros X x l1 l2 eq. rewrite -> eq. reflexivity.
Qed.


Theorem combine_split: forall X Y (l: list (X*Y)) l1 l2,
    split l = (l1,l2) ->
    combine l1 l2 = l.
Proof.
    intros X Y l. induction l as [| (x,y) l'].
    Case "l = nil". intros l1 l2 eq. inversion eq. reflexivity.
    Case "l = x :: xs".
        intros l1 l2 eq.
        destruct l1 as [| x' l1'].
        simpl. inversion eq.
        destruct l2 as [| y' l2'].
        simpl. inversion eq.
        simpl. inversion eq.
        (* (split l') is either (nil,nil) or (xs,ys) *)
        destruct (split l') as (xs,ys). (* key step *)
        apply eq_cons.
        apply IHl'. simpl. reflexivity.
Qed.

Definition split_combine_statement: Prop :=
    forall (X : Type) (l1 l2 : list X),
    length l1 = length l2 ->
    split (combine l1 l2) = (l1,l2).

Theorem split_combine: split_combine_statement.
Proof.
    unfold split_combine_statement.
    intros X l1. induction l1 as [| x xs].
    Case "l1 = nil".
        intros l2 eq. simpl. simpl in eq. destruct l2.
        reflexivity. inversion eq.
    Case "l1 = x :: xs".
        intros l2 eq. destruct l2 as [| y ys].
        simpl. inversion eq. simpl.
        inversion eq. apply IHxs in H0.  (* key step *)
        (* (split (combine xs ys)) is 
                       either (nil,nil) or (xs',ys') *)
        destruct (split (combine xs ys)) as (xs',ys').
        simpl. inversion H0. reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
    if beq_nat n 3 then true
    else if beq_nat n 3 then true
    else false.

Theorem sillyfun1_odd: forall (n : nat),
    sillyfun1 n = true ->
    oddb n = true.
Proof.
    intros n eq. unfold sillyfun1 in eq.
    remember (beq_nat n 3) as e3.
    destruct (e3).
    Case "e3 = true".
        apply beq_nat_eq in Heqe3.
        rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
        inversion eq. 
Qed.

Theorem bool_fn_applied_thrice:
    forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
    intros f b. 
    remember (f b) as fb. destruct fb.
    remember (f true) as ftrue. destruct ftrue.
    symmetry. apply Heqftrue.
    rewrite -> Heqfb.
    remember (f false) as ffalse. destruct ffalse.
    apply Heqfb. destruct b.
    apply Heqftrue.
    apply Heqffalse.
    remember (f false) as ffalse. destruct ffalse. destruct b.
    symmetry. apply Heqfb.
    remember (f true) as ftrue. destruct ftrue.
    rewrite -> Heqfb. apply Heqffalse.
    reflexivity.
    symmetry. apply Heqffalse.
Qed.

Theorem  override_same: forall {X:Type} x1 k1 k2 (f : nat->X),
    f k1 = x1 ->
    (override f k1 x1) k2 = f k2.
Proof.
    intros X x1 k1 k2 f eq. unfold override.
    remember (beq_nat k1 k2) as k1k2eq.
    destruct k1k2eq.
    Case "k1 = k2".
        rewrite <- eq. apply beq_nat_eq in Heqk1k2eq.
        rewrite -> Heqk1k2eq. reflexivity.
    Case "k1 <> k2".
        reflexivity.
Qed.

Example trans_eq_example: forall (a b c d e f : nat),
    [a,b] = [c,d] ->
    [c,d] = [e,f] ->
    [a,b] = [e,f].
Proof.
    intros a b c d e f eq1 eq2.
    rewrite -> eq1. rewrite -> eq2. reflexivity.
Qed.

Theorem trans_eq: forall {X:Type} (n m o : X),
    n = m -> m = o -> n = o.
Proof.
    intros X n m o eq1 eq2.
    rewrite -> eq1. apply eq2.
Qed.

Example trans_eq_example': forall (a b c d e f : nat),
    [a,b] = [c,d] ->
    [c,d] = [e,f] ->
    [a,b] = [e,f].
Proof.
    intros a b c d e f eq1 eq2.
    apply trans_eq with (m:=[c,d]).
    apply eq1. apply eq2.
Qed.

Theorem override_permute:
    forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
    false = beq_nat k2 k1 ->
    (override (override f k2 x2) k1 x1) k3 =
    (override (override f k1 x1) k2 x2) k3.
Proof.
    intros X x1 x2 k1 k2 k3 f eq1. unfold override. 
    remember (beq_nat k1 k3) as k1k3eq.
    remember (beq_nat k2 k3) as k2k3eq.
    destruct k1k3eq.
    Case "k1 = k3".
        destruct k2k3eq.
        SCase "k2 = k3".
            apply beq_nat_eq in Heqk1k3eq. 
            apply beq_nat_eq in Heqk2k3eq.
            rewrite -> Heqk1k3eq in eq1.
            rewrite -> Heqk2k3eq in eq1.
            rewrite <- beq_nat_refl in eq1.
            inversion eq1.
        SCase "k2 <> k3".
            reflexivity.
    Case "k1 <> k2".
        destruct k2k3eq.
        SCase "k2 = k3".
            reflexivity.
        SCase "k2 <> k2".
            reflexivity.
Qed.

Example trans_eq_exercise: forall (n m o p : nat),
    m = (minustwo o) ->
    (n + p) = m ->
    (n + p) = (minustwo o).
Proof.
    intros n m o p eq1 eq2.
    apply trans_eq with m.
    apply eq2. apply eq1.
Qed.

Lemma beq_nat_eq': forall (n m : nat),
    n = m ->
    true = beq_nat n m.
Proof.
    intros n m eq1.
    rewrite -> eq1. apply beq_nat_refl.
Qed.

Theorem beq_nat_trans: forall n m p,
    true = beq_nat n m ->
    true = beq_nat m p ->
    true = beq_nat n p.
Proof.
    intros n m p eq1 eq2.
    apply beq_nat_eq in eq1. apply beq_nat_eq in eq2.
    apply beq_nat_eq'.    
    apply trans_eq with m.
    apply eq1. apply eq2.
Qed.

Theorem beq_nat_sym: forall (n m : nat),
    beq_nat n m = beq_nat m n.
Proof.
    intros n m. remember (beq_nat n m) as nmeq. destruct nmeq.
    Case "true".
        apply beq_nat_eq in Heqnmeq. rewrite -> Heqnmeq.
        apply beq_nat_refl.
    Case "false".
        remember (beq_nat m n) as mneq. destruct mneq.
        apply beq_nat_eq in Heqmneq.
        rewrite -> Heqmneq in Heqnmeq.
        rewrite <- beq_nat_refl in Heqnmeq.
        inversion Heqnmeq.
        reflexivity. 
Qed.

Theorem filter_exercise: forall (X : Type) (test : X -> bool)
                                (x : X) (l lf : list X),
    filter test l = x :: lf ->
    test x = true.
Proof.
    intros X test x l lf H. generalize dependent lf.
    induction l as [| x' xs ].
    Case "l = nil".
        simpl. intros lf eq. inversion eq.
    Case "l = x' :: xs".
        simpl. intros lf eq. remember (test x') as tx'.
        destruct tx'.
        SCase "test x' = true".        
            inversion eq. rewrite <- H0. symmetry. assumption.
        SCase "test x' = false". 
            apply IHxs in eq. assumption.
Qed.

Fixpoint forallb {X:Type} (test : X -> bool) (l : list X)
    : bool :=
    match l with
    | nil => true
    | x :: xs => if test x
                then forallb test xs
                else false
    end.

Fixpoint existsb {X:Type} (test : X -> bool) (l : list X)
    : bool :=
    match l with
    | nil => false
    | x :: xs => if test x
                then true
                else existsb test xs
    end.

Definition existsb' {X:Type} (test : X -> bool) (l : list X)
    : bool :=
    negb (forallb (fun x => negb (test x)) l).

Example test_forallb:
    forallb oddb [1,3,5] = true.
Proof. reflexivity. Qed.

Example test_existsb:
    existsb oddb [0,0,1] = true.
Proof. reflexivity. Qed.

Example test_existsb':
    existsb' oddb [0,0,1] = true.
Proof. reflexivity. Qed.

Theorem existsb_eq: forall {X:Type} (test : X->bool) (l : list X),
    existsb test l = existsb' test l.
Proof.
    intros X test l. induction l as [| x xs].
    Case "l = nil".
        simpl. unfold existsb'. simpl. reflexivity.
    Case "l = x :: xs".
        simpl. remember (test x) as testx. destruct testx.
        SCase "test x = true".
            unfold existsb'. simpl. rewrite <- Heqtestx.
            simpl. reflexivity.
        SCase "test x = false".
            rewrite -> IHxs.
            unfold existsb'. simpl. rewrite <- Heqtestx. simpl.
            reflexivity.
Qed.

