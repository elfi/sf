Require Export MoreCoq.

Inductive beautiful : nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem three_is_beautiful: beautiful 3.
Proof.
    apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
    apply b_sum with (n:=3) (m:=5).
    apply b_3.
    apply b_5.
Qed.

Check b_sum.
Check (b_sum 3 5 b_3 b_5). (* b_sum 3 5 b_3 b_5 : beautiful (3+5) *)

Theorem eight_is_beautiful': beautiful 8.
Proof.
    apply (b_sum 3 5 b_3 b_5).
Qed.

Theorem eight_is_beautiful'': beautiful 8.
Proof.
    Show Proof.
    apply b_sum with (n:=3) (m:=5).
    Show Proof.
    apply b_3.
    Show Proof.
    apply b_5.
    Show Proof.
Qed.

Definition eight_is_beautiful''': beautiful 8 :=
    b_sum 3 5 b_3 b_5.

Print eight_is_beautiful.
Print eight_is_beautiful'.
Print eight_is_beautiful''.
Print eight_is_beautiful'''.

Theorem six_is_beautiful: 
    beautiful 6.
Proof.
    apply (b_sum 3 3 b_3 b_3).
Qed.

Definition six_is_beautiful': beautiful 6 :=
    b_sum 3 3 b_3 b_3.

Theorem nine_is_beautiful:
    beautiful 9.
Proof.
    apply (b_sum 3 6).
    apply (b_3).
    apply (b_sum 3 3 b_3 b_3).
Qed.

Definition nine_is_beautiful': beautiful 9 := 
    b_sum 3 6 b_3 (b_sum 3 3 b_3 b_3).

Print nine_is_beautiful.
Print nine_is_beautiful'.

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
    intros n H.
    apply b_sum.
    apply b_3.
    apply H.
Qed.

Definition b_plus3': forall n, beautiful n -> beautiful (3+n) :=
    fun n => fun H : beautiful n => b_sum 3 n b_3 H.

Check b_plus3'.

Definition b_plus3'' (n : nat) (H : beautiful n) : beautiful (3+n) :=
    b_sum 3 n b_3 H.

Check b_plus3''.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
    intros n H.
    simpl. rewrite -> plus_0_r.
    apply (b_sum n n H H).
Qed.

Lemma plusnn_eq_2n: forall n, beautiful (n+n) -> beautiful (2*n).
Proof.
    intros n H.
    simpl.
    rewrite -> plus_0_r.
    assumption.
Qed.

Definition b_times2': forall n, beautiful n -> beautiful (2*n) :=
    fun n => fun H : beautiful n =>
        plusnn_eq_2n n (b_sum n n H H).

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
    intros n m H. induction m as [| m'].
    Case "m = O".
        simpl. apply b_0.
    Case "m = S m'".
        simpl. apply (b_sum n (m' * n) H IHm').
Qed.

Inductive gorgeous: nat -> Prop :=
| g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

Theorem gorgeous__beautiful: forall n,
    gorgeous n -> beautiful n.
Proof.
    intros n H.
    induction H as [| n' | n'].
    Case "g_0".
        apply b_0.
    Case "g_plus3".
        apply (b_sum 3 n' b_3 IHgorgeous).
    Case "g_plus5".
        apply (b_sum 5 n' b_5 IHgorgeous).
Qed.

Theorem gorgeous_plus13: forall n,
    gorgeous n -> gorgeous (13+n).
Proof.
    intros n H.
    apply (g_plus3 (10+n) (g_plus5 (5+n) (g_plus5 n H))).
Qed.

Definition gorgeous_plus13_po :=
    fun n => fun H => (g_plus3 (10+n) (g_plus5 (5+n) (g_plus5 n H))).

Print gorgeous_plus13.
Print gorgeous_plus13_po.

Theorem gorgeous_sum: forall n m,
    gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
    intros n m Hn Hm.
    induction Hn as [| n' | n' ].
    Case "g_0".
        simpl. apply Hm.
    Case "g_plus3".
        apply (g_plus3 (n' + m) IHHn).
    Case "g_plus5".
        apply (g_plus5 (n' + m) IHHn).
Qed.

Theorem beautiful__gorgeous: forall n, beautiful n -> gorgeous n.
Proof.
    intros n H.
    induction H as [| | | n' m' ].
    Case "b_0".
        apply g_0.
    Case "b_3".
        apply (g_plus3 0 g_0).
    Case "b_5".
        apply (g_plus5 0 g_0).
    Case "b_sum".
        apply (gorgeous_sum n' m' IHbeautiful1 IHbeautiful2).
Qed.

Lemma helper_g_times2: forall x y z, x + (z + y) = z + x + y.
Proof.
    intros x y z.
    rewrite -> plus_swap.    
    rewrite -> plus_assoc.
    reflexivity.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
    intros n H. simpl. rewrite -> plus_0_r.
    induction H as [| n' | n' ].
    Case "g_0".
        simpl. apply g_0.
    Case "g_plus3 n'".
        rewrite -> helper_g_times2. simpl.
        apply (g_plus3 (3 + n' + n') (g_plus3 (n' + n') IHgorgeous)).
    Case "g_plus5 n'".
        rewrite -> helper_g_times2. simpl.        
        apply (g_plus5 (5 + n' + n') (g_plus5 (n' + n') IHgorgeous)).
Qed.

Definition even (n:nat) : Prop :=
    evenb n = true.

Check even.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n:nat, ev n -> ev (S (S n)).

Check ev.

Theorem double_even: forall n,
    ev (double n).
Proof.
    intro n. induction n as [| n'].
    Case "n = O".
        simpl. apply ev_0.
    Case "n = S n'".
        simpl. apply (ev_SS (double n') IHn').
Qed.

Theorem ev_minus2: forall n,
    ev n -> ev (pred (pred n)).
Proof.
    intros n H.
    destruct H as [| n' E' ].
    Case "ev_0".
        simpl. apply ev_0.
    Case "ev_SS n' E'".
        simpl. apply E'. 
Qed.

Theorem ev__even: forall n, ev n -> even n.
Proof.
    intros n E. induction E as [| n' E'].
    Case "ev_0".
        unfold even. simpl. reflexivity.
    Case "ev_SS n' E'".
        unfold even. simpl. apply IHE'.
Qed.


