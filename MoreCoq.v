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
