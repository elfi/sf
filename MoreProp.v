Require Export "Prop".

Check (2 + 2 = 4).
Check (ble_nat 3 2 = false).
Check (beautiful 8).
Check (2 + 2 = 5).
Check (beautiful 4).

Theorem plus_2_2_is_4:
    2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact: Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true:
    plus_fact.
Proof.  unfold plus_fact. reflexivity. Qed.

Check (even 4).
Check (even 3).
Check even.

Definition between (n m o : nat) : Prop :=
    andb (ble_nat n o) (ble_nat o m) = true.

Definition teen: nat->Prop := between 13 19.

Definition true_for_zero (P:nat->Prop) : Prop :=
    P 0.

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
    forall n, P n.

Definition preserved_by_S (P:nat->Prop) : Prop :=
    forall n, P n -> P (S n).

Definition combine_odd_even (Podd Peven : nat->Prop) : nat -> Prop :=
    fun n => match (oddb n) with
             | true => Podd n
             | false => Peven n
             end.

Theorem combine_add_even_intro:
    forall (Podd Peven : nat->Prop) (n:nat),
      (oddb n = true -> Podd n) ->
      (oddb n = false -> Peven n) ->
      combine_odd_even Podd Peven n.
Proof.
    intros Podd Peven n Eq1 Eq2.
    unfold combine_odd_even.
    remember (oddb n) as oddbn. destruct oddbn.
    apply Eq1. reflexivity.
    apply Eq2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd:
    forall (Podd Peven : nat->Prop) (n:nat),
      combine_odd_even Podd Peven n ->
      oddb n = true ->
      Podd n.
Proof.
    intros Podd Peven n Eq1 Eq2. unfold combine_odd_even in Eq1.
    destruct (oddb n).
    Case "true". apply Eq1.
    Case "false". inversion Eq2.
Qed.

Theorem combine_odd_even_elim_even:
    forall (Podd Peven : nat->Prop) (n:nat),
      combine_odd_even Podd Peven n ->
      oddb n = false ->
      Peven n.
Proof.
    intros Podd Peven n Eq1 Eq2. unfold combine_odd_even in Eq1.
    destruct (oddb n).
    Case "true". inversion Eq2.
    Case "false". apply Eq1.
Qed.

Fixpoint
 true_upto_n__true_everywhere (n : nat) (P : nat -> Prop)
 : Prop :=
    match n with
    | 0 => forall m:nat, P m
    | S n' => P n -> true_upto_n__true_everywhere n' P 
    end.

Check true_upto_n__true_everywhere.
Eval simpl in (true_upto_n__true_everywhere 3 (fun n => even n)).

Example true_upto_n_example:
    (true_upto_n__true_everywhere 3 (fun n => even n))
    = (even 3 -> even 2 -> even 1 -> forall m:nat, even m).
Proof. reflexivity. Qed.

