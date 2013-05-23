Require Export Lists.

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check nil.
Check cons.
Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X : Type) (l : list X) : nat :=
    match l with
    | nil => 0
    | cons x xs => S (length X xs)
    end.

Example test_length1:
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2:
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

(* One does not put the type X into the pattern match
*  as l1 is already known to be of type list X.
*  In contrast, after => we need to supply the type X
*  to the cons constructor to denote which kind of list
*  we are building with it *)
Fixpoint app (X : Type) (l1 l2 : list X) : list X :=
    match l1 with
    | nil => l2
    | cons h l1' => cons X h (app X l1' l2) 
    end.

Fixpoint snoc (X : Type) (l : list X) (v : X) : list X :=
    match l with
    | nil => cons X v (nil X)
    | cons h l' => cons X h (snoc X l' v)
    end.

Fixpoint rev (X : Type) (l : list X) : list X :=
    match l with
    | nil => nil X
    | cons h l' => snoc X (rev X l') h
    end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
    = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2 :
    rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.


