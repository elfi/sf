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


