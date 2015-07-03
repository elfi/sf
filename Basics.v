Definition admit {T : Type} : T. Admitted.

(* simple enumerated type *)

Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

(* and a function day -> day *)
Definition next_day (d : day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => sunday
    | sunday => monday
    end.

Eval compute in (next_day monday).

Example test_next_day : next_day monday = tuesday.
Proof. reflexivity. Qed.

(* Booleans *)
Inductive bool : Type :=
| true : bool
| false : bool.


Definition bool_recursor :
    forall C : Type, C -> C -> bool -> C :=
    fun (C : Type) (c1 : C) (c2 : C) (b : bool) =>
    match b with
    | true => c1
    | false => c2
    end.

Definition bool_induction :
    forall (C : bool -> Type), C true -> C false -> forall (b : bool), C b :=
    fun (C : bool -> Type) (c1 : C true) (c2 : C false) (b : bool) =>
    match b with
    | true => c1
    | false => c2
    end.

(* Lets check with generated induction *)
Theorem bool_induction_check :
    bool_induction = bool_rect.
Proof.
    unfold bool_induction, bool_rect.
    reflexivity.
Qed.

(* recursor in just a non-dependent induction *)
Theorem bool_recursor_via_induction :
    forall C : Type, bool_recursor C = bool_induction (fun _ : bool => C).
Proof.
    unfold bool_recursor, bool_induction.
    reflexivity.
Qed.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition negb_via_recursor := bool_recursor bool false true.

Theorem negb_via_recursor_correct : negb = negb_via_recursor.
Proof.
    unfold negb, negb_via_recursor.
    unfold bool_recursor.
    reflexivity.
Qed.

Inductive unit : Type :=
| tt : unit.

Definition unit_recursor :
    forall (C : Type), C -> unit -> C :=
    fun (C : Type) (c : C) (u : unit) =>
    match u with
    | tt => c
    end.

Definition unit_induction :
    forall (C : unit -> Type), C tt -> forall u : unit, C u :=
    fun (C : unit -> Type) (c : C tt) (u : unit) => 
    match u with
    | tt => c
    end.

Theorem unit_induction_check :
    unit_induction = unit_rect.
Proof.
    unfold unit_induction, unit_rect.
    reflexivity.
Qed.

Theorem unit_recursor_via_induction :
    forall C : Type,
      unit_recursor C = unit_induction (fun _:unit => C).
Proof.
    unfold unit_recursor, unit_induction.
    reflexivity.
Qed.

Inductive False : Type := .
Print False_rect.

Definition False_recursor :
    forall (C : Type), False -> C :=
    fun (C : Type) (f : False) =>
    match f with end.

Definition False_induction :
    forall (C : False -> Type), forall f : False, C f :=
    fun (C : False -> Type) (f : False) =>
    match f with end.

Theorem False_induction_check :
    False_induction = False_rect.
Proof.
    unfold False_induction, False_rect.
    reflexivity.
Qed.

Theorem False_recursor_via_induction :
    forall C : Type,
      False_recursor C = False_induction (fun _:False => C).
Proof.
    unfold False_recursor, False_induction.
    reflexivity.
Qed.

Inductive maybe_nat : Type :=
| NoneNat : maybe_nat
| SomeNat : nat -> maybe_nat.

Definition maybe_nat_recursor :
    forall (C : Type), C -> (nat -> C) -> maybe_nat -> C :=
    fun (C : Type) (c1 : C) (f : nat -> C) (m : maybe_nat) =>
    match m with
    | NoneNat => c1
    | SomeNat x => f x
    end.

Definition maybe_nat_induction :
    forall (C : maybe_nat -> Type),
      C NoneNat -> (forall n:nat, C (SomeNat n)) -> forall m : maybe_nat, C m :=
    fun (C : maybe_nat -> Type) (c1 : C NoneNat) (f : forall n:nat, C (SomeNat n))
        (m : maybe_nat) =>
    match m with
    | NoneNat => c1
    | SomeNat x => f x
    end.

Theorem maybe_nat_induction_check :
    maybe_nat_induction = maybe_nat_rect.
Proof.
    unfold maybe_nat_induction, maybe_nat_rect.
    reflexivity.
Qed.

Inductive maybe (a : Type) : Type :=
| None : maybe a
| Some : a -> maybe a.

Definition maybe_recursor :
    forall (a : Type) (C : Type), C -> (a -> C) -> maybe a -> C :=
    fun (a C : Type) (c1 : C) (f : a -> C) (m : maybe a) =>
    match m with
    | None => c1
    | Some x => f x
    end.

Definition maybe_induction :
    forall (a : Type) (C : maybe a -> Type),
      C (None a)  -> (forall n:a, C (Some a n)) -> forall m : maybe a, C m :=
    fun (a : Type) (C : maybe a -> Type) (c1 : C (None a))
        (f : forall n:a, C (Some a n)) (m : maybe a) =>
    match m with
    | None => c1
    | Some x => f x
    end.

Theorem maybe_induction_check :
    maybe_induction = maybe_rect.
Proof.
    unfold maybe_induction, maybe_rect.
    reflexivity.
Qed.

Module Nats.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint nat_recursor :
    forall C : Type, C -> (nat -> C -> C) -> nat -> C :=
    fun (C : Type) (c1 : C) (f : nat -> C -> C) (n : nat) =>
    match n with
    | O => c1
    | S x => f x (nat_recursor C c1 f x) 
    end.

Definition nat_induction :
    forall (C : nat -> Type),
      C O -> (forall n:nat, C n -> C (S n)) -> forall n:nat, C n :=
    fun (C : nat -> Type) (c1 : C O) (f : forall n:nat, C n -> C (S n))
        (n : nat) =>
    match n with
    | O => c1
    | S x => f


End Nats.
