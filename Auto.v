Require Export Imp.

Ltac inv H := inversion H; subst; clear H.

Example auto_example_1: forall (P Q R : Prop),
    (P -> Q) -> (Q -> R) -> P -> R.
Proof.
    intros P Q R H1 H2 H3.
    apply H2. apply H1. assumption.
Qed.

Example auto_example_1': forall (P Q R : Prop),
    (P -> Q) -> (Q -> R) -> P -> R.
Proof.
    intros. auto.
Qed.

Example auto_example_2: forall P Q R S T U : Prop,
    (P -> Q) ->
    (P -> R) ->
    (T -> R) ->
    (S -> T -> U) ->
    ((P -> Q) -> (P -> S)) ->
    T ->
    P ->
    U.
Proof. auto. Qed.

Example auto_example_3: forall (P Q R S T U : Prop),
    (P -> Q) -> (Q -> R) -> (R -> S) ->
    (S -> T) -> (T -> U) -> P -> U.
Proof.
    auto.
    auto 6.
Qed.

Example auto_example_4: forall P Q R : Prop,
    Q ->
    (Q -> R) ->
    P \/ (Q /\ R).
Proof. auto. Qed.

Example auto_example_5: 2 = 2.
Proof. info_auto. Qed.

Lemma le_antisym: forall n m : nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6: forall n m p : nat,
    (n <= p -> (n <= m /\ m <= n)) ->
    n <= p ->
    n = m.
Proof.
    intros.
    auto.
    auto using le_antisym.
Qed.

Hint Resolve le_antisym.

Example auto_example_6': forall n m p : nat,
    (n <= p -> (n <= m /\ m <= n)) ->
    n <= p ->
    n = m.
Proof. auto. Qed.

Definition is_fortytwo x := x = 42.

Example auto_example_7: forall x, (x <= 42 /\ 42 <= x) ->
    is_fortytwo x.
Proof.
    auto.
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7': forall x, (x <= 42 /\ 42 <= x) ->
    is_fortytwo x.
Proof.
    auto.
Qed.

Hint Constructors ceval.

Definition st12 := update (update empty_state X 1) Y 2.
Definition st21 := update (update empty_state X 2) Y 1.

Example auto_example_8: exists s',
    (IFB (BLe (AId X) (AId Y))
         THEN (Z ::= AMinus (AId Y) (AId X))
         ELSE (Y ::= APlus (AId X) (AId Z))
     FI) / st21 || s'.
Proof.
   eexists. info_auto.
Qed.

Example auto_example_8': exists s',
    (IFB (BLe (AId X) (AId Y))
         THEN (Z ::= AMinus (AId Y) (AId X))
         ELSE (Y ::= APlus (AId X) (AId Z))
     FI) / st21 || s'.
Proof.
   eexists. info_auto.
Qed.


