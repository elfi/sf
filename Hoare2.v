Require Export Hoare.

Definition reduce_to_zero' : com :=
    WHILE BNot (BEq (AId X) (ANum 0)) DO
        X ::= AMinus (AId X) (ANum 1)
    END.

Theorem reduce_to_zero_correct' :
    {{ fun st => True }}
    reduce_to_zero'
    {{ fun st => st X = 0 }}.
Proof.
    unfold reduce_to_zero'.
    (* transform the post-condition; then hoare_while *)
    eapply hoare_consequence_post.
    Case "Hoare_while".
        apply hoare_while.
        (* transform pre-condition; then hoare_assg *)
        eapply hoare_consequence_pre.
        SCase "assignment".
            apply hoare_asgn.
        SCase "pre-condition weakening".
            intros st [HT GuardTrue]. unfold assn_sub. apply HT.
    Case "strengthening the post-condition".
        intros st [HT GuardFalse].
        unfold bassn in GuardFalse. simpl in GuardFalse.
        SearchAbout [not true].
        rewrite -> not_true_iff_false in GuardFalse.
        SearchAbout [negb false].
        rewrite negb_false_iff in GuardFalse.
        SearchAbout [beq_nat true].
        apply beq_nat_true in GuardFalse.
        apply GuardFalse.
Qed.

(* slow_assignment:

   loop invariant is X + Y = m

    {{ X = m }}
    Y ::= 0;
    {{ X + Y = m }}
    WHILE X <> 0 DO
        {{ X + Y = m /\ X <> 0 }} ->>   (OK)
        {{ (X - 1) + (Y + 1) = m }}
        X ::= X - 1;
        {{ X + (Y + 1) = m }}
        Y ::= Y + 1;
        {{ X + Y = m }}
    END
    {{ X + Y = m /\ ~(X <> 0) }} ->>    (OK)
    {{ Y = m }}

*)

(* add_slowly_decoration:

   loop invariant is X + Z = m + n

{{ X = m /\ Z = n }} ->>                (OK)
{{ X + Z = m + n }}
WHILE X <> 0 DO
    {{ X + Z = m + n /\ X <> 0 }} ->>   (OK)
    {{ (X - 1) + (Z + 1) = m + n }}
    Z ::= Z + 1;
    {{ (X - 1) + Z = m + n }}
    X ::= X - 1;
    {{ X + Z = m + n }}
END
{{ X + Z = m + n /\ ~(X <> 0) }} ->>    (OK)
{{ Z = n + m }}

*)

Fixpoint parity x :=
    match x with
    | 0 => 0
    | 1 => 1
    | S (S x') => parity x'
    end.

Lemma parity_ge_2: forall x,
    2 <= x ->
    parity (x - 2) = parity x.
Proof.
    induction x; intro.
    Case "base". reflexivity.
    Case "step". destruct x.
        SCase "O". inversion H. inversion H1.
        SCase "S ..". simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2: forall x,
    ~ ( 2 <= x ) ->
    parity x = x.
Proof.
    induction x; intro.
    Case "base". reflexivity.
    Case "step". unfold not in H. destruct x.
        SCase "O". reflexivity.
        SCase "S ..". apply ex_falso_quodlibet. apply H. omega.
Qed.

Theorem parity_correct: forall m,
    {{ fun st => st X = m }}
    WHILE BLe (ANum 2) (AId X) DO
        X ::= AMinus (AId X) (ANum 2)
    END
    {{ fun st => st X = parity m }}.
Proof.
    intro m.
    (* we nee to adjust both the pre- and post-condition *)
    eapply hoare_consequence.
    Case "hoare_while".
        (* loop with its invariant; crucial step *)
        apply hoare_while
            with (P := (fun st => parity (st X) = parity m)).
        (* fix the inner part of the loop *)
        eapply hoare_consequence_pre.
        SCase "assignment".
            apply hoare_asgn.
        SCase "assignment pre-condition weakening".
            unfold assert_implies, assn_sub, update. simpl.
            intros st [H0 H1]. rewrite <- H0. apply parity_ge_2.
            unfold bassn, beval, aeval in H1.
            apply ble_nat_true in H1. apply H1.
    Case "weakening the pre-condition".
        unfold assert_implies. intros st H.
        rewrite -> H. reflexivity.
    Case "strengthening the post-condition".
        unfold bassn, assert_implies. intros st [H0 H1].
        rewrite <- H0. symmetry. apply parity_lt_2.
        unfold beval, aeval in H1.
        (* destruct and remember *)
        destruct (ble_nat 2 (st X)) eqn:Heqle.
        apply ex_falso_quodlibet. apply H1. reflexivity.
        apply ble_nat_false in Heqle. apply Heqle.
Qed.


