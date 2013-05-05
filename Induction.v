Require Export Basics.
Require String. Open Scope string_scope.

Ltac move_to_top x :=
    match reverse goal with
    | H : _ |- _ => try move x after H
    end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
    let H := fresh in
    assert (x = v) as H by reflexivity;
    clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
    first [
      set (x := name); move_to_top x
    | assert_eq x name; move_to_top x
    | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
Tactic Notation "SSSSSSSSCase" constr(name) := Case_aux SSSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
    andb b c = true -> b = true.
Proof.
    intros b c H.
    destruct b.
    Case "b = true".
      reflexivity.
    Case "b = false".
      rewrite <- H.
      reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
    intros b c H. destruct c.
    Case "c = true".
      reflexivity.
    Case "c = false".
      rewrite <- H.
      destruct b.      
      SCase "b = true".
        reflexivity.
      SCase "b = false".
        reflexivity.
Qed.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n,
    minus n n = 0.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0". reflexivity.
    Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

