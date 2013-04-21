Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d:day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
    (next_weekday (next_weekday saturday)) = tuesday.
Proof.  simpl.  reflexivity.  Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.

Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | false => true
    | true => negb b2
    end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
    match b1 with
    | true => andb b2 b3
    | false => false
    end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.

Module Playground1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n:nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End Playground1.

Definition minustwo (n:nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

Definition oddb (n:nat) : bool :=
    negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.

Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m:nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O, _ => O
    | n, O => n
    | S n', S m' => minus n' m'
    end.

Eval simpl in (minus 5 3).

End Playground2.

Fixpoint exp (base power:nat) : nat :=
    match power with
    | O => 1
    | S n' => mult base (exp base n')
    end.

Fixpoint factorial (n:nat) : nat :=
    match n with
    | O => 1
    | S n' => mult n (factorial n')
    end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
    (at level 50, left associativity)
    : nat_scope.
Notation "x - y" := (minus x y)  
    (at level 50, left associativity)
    : nat_scope.
Notation "x * y" := (mult x y)  
    (at level 40, left associativity) 
    : nat_scope.

Check ((0 + 1) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
    match n, m with
    | O, O => true
    | O, S m' => false
    | S n', O => false
    | S n', S m' => beq_nat n' m'
    end.

Fixpoint ble_nat (n m : nat) : bool :=
    match n, m with
    | O, _ => true
    | S n', O => false
    | S n', S m' => ble_nat n' m'
    end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.


