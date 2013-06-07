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

