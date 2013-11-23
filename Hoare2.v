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

(* factorial:

   loop invariant is Y * X! = m!

   {{ X = m }} ->>                         (OK)
   {{ 1 * X! = m! }}
   Y ::= 1;
   {{ Y * X! = m! }}
   WHILE X <> 0 DO
       {{ Y * X! = m! /\ X <> 0 }} ->>     (OK)
       {{ Y * X * (X - 1)! = m! }}
       Y ::= Y * X;
       {{ Y * (X - 1)! = m! }}
       X ::= X - 1;
       {{ Y * X! = m! }}
   END
   {{ Y * X! = m! /\ ~(X <> 0) }} ->>      (OK)
   {{ Y = m! }}
*)

(* min_hoare:

   use:
    Lemma lemma1: forall x y,
        (x = 0) \/ (y = 0) -> min x y = 0.
    Lemma lemma2: forall x y,
        min (x - 1) (y - 1) = (min x y) - 1.

    loop invariant is: min a b = (min X Y) + Z

    {{ True }} ->>                             (OK)
    {{ min a b = min a b}}
    X ::= a;
    {{ min a b = min X b }}
    Y ::= b;
    {{ min a b = min X Y }}
    Z ::= 0;
    {{ min a b = (min X Y) + Z }}
    WHILE (X <> 0 /\ Y <> 0) DO
        {{ min a b = (min X Y) + Z /\
             (X <> 0 /\ Y <> 0)        }} ->>  (OK, lemma2)
        {{ min a b = (min (X - 1) (Y - 1)) + Z + 1 }}
        X ::= X - 1;
        {{ min a b = (min X (Y - 1)) + Z + 1 }}
        Y ::= Y - 1;
        {{ min a b = (min X Y) + Z + 1 }}
        Z ::= Z + 1;
        {{ min a b = (min X Y) + Z }}
    END
    {{ min a b = (min X Y) + Z /\
         ~( X <> 0 /\ Y <> 0)      }} ->>      (OK, lemma1)
    {{ Z = min a b }}
*)

(* two_loops:

   loop invariant is Z = X + Y + c

   {{ True }} ->>                              (OK)
   {{ c = c}}
   X ::= 0;
   {{ c = X + c }}
   Y ::= 0;
   {{ c = X + Y + c }}
   Z ::= c;
   {{ Z = X + Y + c }}
   WHILE X <> a DO
       {{ Z = X + Y + c /\ X <> a }} ->>       (OK)
       {{ Z + 1 = X + 1 + Y + c }}
       X ::= X + 1;
       {{ Z + 1 = X + Y + c }}
       Z ::= Z + 1;
       {{ Z = X + Y + c }}
   END
   {{ Z = X + Y + c /\ X = a }} ->>            (OK)
   {{ Z = a + Y + c }}
   WHILE Y <> b DO
       {{ Z = a + Y + c /\ Y <> b }} ->>       (OK)
       {{ Z + 1 = a + Y + 1 + c }}
       Y ::= Y + 1;
       {{ Z + 1 = a + Y + c }}
       Z ::= Z + 1;
       {{ Z = a + Y + c }}
   END
   {{ Z = a + Y + c /\ Y = b }} ->>            (OK)
   {{ Z = a + b + c }}
*)

(* dpow2_down:

   power series: ( 1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1 )

   loop invariant is Y + 2*Z = 2^(X+2) - 1

   {{ True }} ->>                                   (OK)
   {{ 3 = 4 - 1}}
   X ::= 0;
   {{ 3 = 2^(X+2) - 1 }}
   Y ::= 1;
   {{ Y + 2 = 2^(X+2) -1 }}
   Z ::= 1;
   {{ Y + 2*Z = 2^(X+2) - 1 }}
   WHILE X <> m DO
       {{ Y + 2*Z = 2^(X+2) - 1 /\ X <> m }} ->>    (OK)
       {{ Y + 2*Z + 2*2*Z = 2^(X+3) - 1 }}
       Z ::= 2 * Z;
       {{ Y + Z + 2*Z = 2^(X+3) - 1 }}
       Y ::= Y + Z;
       {{ Y + 2*Z = 2^(X+3) - 1 }}
       X ::= X + 1;
       {{ Y + 2*Z = 2^(X+2) - 1 }}
   END
   {{ Y + 2*Z = 2^(X+2) - 1 /\ X = m }} ->>         (OK)
   {{ Y + 2*Z = 2^(m+2) - 1 }} ->>                  (OK)
   {{ Y = 2^(m+1) - 1 }}
*)

Definition is_wp P c Q :=
    {{ P }} c {{ Q }} /\
    forall P', {{ P' }} c {{ Q }} -> (P' ->> P).

Theorem is_pw_example:
    is_wp (fun st => st Y <= 4)
          (X ::= APlus (AId Y) (ANum 1))
          (fun st => st X <= 5).
Proof.
    split.
    Case "valid precodition".
        eapply hoare_consequence_pre.
        SCase "assignment".
            apply hoare_asgn.
        SCase "weaken precodition".
            unfold assn_sub, assert_implies, update. simpl.
            intros st H. omega.
    Case "weakest precondition".
        intros P' Htriple. unfold assert_implies. intros st HP'.
        unfold hoare_triple in Htriple.
        (* we need to build hypothesis
           H : (X ::= APlus (AId Y) (ANum 1)) / st || st'
           and use it with Htriple *)
        remember (update st X (st Y + 1)) as st'.
        assert (H: ((X ::= APlus (AId Y) (ANum 1)) / st || st')).
            subst st'. apply E_Ass. simpl. reflexivity.
        apply Htriple in H;
            try assumption. (* (P' st) part in Htriple *)
        rewrite Heqst' in H. unfold update in H. simpl in H. omega.
Qed.

Theorem hoare_sgn_weakest: forall Q X a,
    is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
    intros Q X a. unfold is_wp. split.
    Case "valid precondition".
        apply hoare_asgn.
    Case "weakest precondition".
        intro P'. unfold assert_implies. intros Htriple st HP'.
        unfold assn_sub. unfold hoare_triple in Htriple.
        remember (update st X (aeval st a)) as st'.
        apply Htriple with (st:= st).
        subst st'. apply E_Ass. reflexivity.
        assumption.
Qed.

Module Himp2.
Import Himp.

Lemma hoare_havoc_weakest: forall (P Q : Assertion) (X : id),
    {{ P }} HAVOC X {{ Q }} ->
    P ->> havoc_pre X Q.
Proof.
    intros P Q X Htriple. unfold assert_implies. intros st HP.
    unfold havoc_pre. intro n. unfold hoare_triple in Htriple.
    remember (update st X n) as st'.
    apply Htriple with (st:=st);
        try assumption.  (* (P st) part in Htriple *)
    subst st'. apply E_Havoc.
Qed.

End Himp2.


