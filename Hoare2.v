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
    Case "strenghening the post-condition".
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


