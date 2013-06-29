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

Theorem ev_sum: forall n m,
    ev n -> ev m -> ev (n + m).
Proof.
    intros n m En Em. induction En as [| n' En'].
    Case "ev_0".
        simpl. apply Em.
    Case "ev_SS n' En'".
        simpl. apply (ev_SS (n' + m) IHEn').
Qed.

Theorem SSev_ev_secondtry: forall n,
    ev (S (S n)) -> ev n.
Proof.
    intros n E. remember (S (S n)) as n2.
    destruct E. inversion Heqn2. inversion Heqn2. rewrite <- H0. apply E.
Qed.

Theorem SSev__even: forall n,
    ev (S (S n)) -> ev n.
Proof.
    intros n E. inversion E as [| n' E']. apply E'.
Qed.

Theorem SSSSev__even: forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
    intros n E.
    inversion E as [| n' E']. inversion E' as [| n'' E''].
    apply E''.
Qed.

Theorem even5_nonsense:
    ev 5 -> 2 + 2 = 9.
Proof.
    intro H.
    inversion H as [| n E ]. inversion E as [| n' E']. inversion E'.
Qed.

Theorem ev_minus2': forall n,
    ev n -> ev (pred (pred n)).
Proof.
    intros n E. inversion E as [| n' E'].
    Case "E = ev 0". simpl. apply ev_0.
    Case "E = ev_SS n' E'". simpl. apply E'.
Qed.

Theorem  ev_ev__ev: forall n m,
    ev (n+m) -> ev n -> ev m.
Proof.
    intros n m E1 E2. induction E2 as [| n' E2'].
    Case "E2 = ev_0".
         simpl in E1. apply E1.
    Case "E2 = ev_SS n' E2'".
         simpl in E1. apply IHE2'. apply SSev__even in E1. apply E1.
Qed.

Theorem ev_plus_plus : forall n m p,
    ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
    intros n m p E1.     
    apply ev_ev__ev. replace (n + p + (m + p)) with ((double p) + (n + m)).
    apply ev_sum. apply double_even. apply E1.
    Case "proof of replace".
        rewrite -> double_plus. rewrite -> plus_swap.
        rewrite -> (plus_comm m p). rewrite <- plus_assoc.
        remember (p + m) as pm. rewrite -> plus_assoc. reflexivity. 
Qed.

SearchAbout beautiful.
Definition b_16: beautiful 16 :=
    b_sum 5 11 b_5 (b_sum 5 6 b_5 (b_sum 3 3 b_3 b_3)).

Inductive pal {X:Type} : list X -> Prop :=
| pal_nil   : pal nil
| pal_singl : forall x:X, pal [x]
| pal_sum   : forall (x:X) (l:list X), 
                pal l ->  pal ( x :: l ++ [x] ).

Lemma snoc_append: forall {X : Type} (x:X) (l : list X),
    snoc l x = l ++ [x].
Proof.
    intros X x l. induction l.
    simpl. reflexivity.
    simpl.  rewrite -> IHl. reflexivity.
Qed.

Lemma app_assoc: forall {X : Type} (l1 l2 l3 : list X),
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros X l1 l2 l3. induction l1.
    simpl. reflexivity.
    simpl. rewrite -> IHl1. reflexivity.
Qed.

Theorem pal_thm1: forall {X : Type} (l : list X),
    pal (l ++ rev l).
Proof.
    intros X l. induction l.
    Case "nil".
       simpl. apply (pal_nil).
    Case "cons".
       simpl. rewrite -> snoc_append.
       rewrite <- app_assoc.
       remember (l ++ rev l) as l'.
       apply (pal_sum x l').       
       apply IHl.
Qed.

Lemma app_nil_end: forall {X : Type} (l : list X),
    l ++ nil = l.
Proof.
    intros X l. induction l.
    reflexivity.
    simpl. rewrite -> IHl. reflexivity.
Qed.

Lemma rev_snoc: forall {X : Type} (x:X) (l : list X),
    rev (snoc l x) = x :: rev l.
Proof.
    intros X x l. induction l.
    reflexivity.
    simpl. rewrite -> IHl. simpl. reflexivity. 
Qed.

Lemma rev_involutive: forall {X : Type} (l : list X),
    rev (rev l) = l.
Proof.
    intros X l. induction l.
    simpl. reflexivity.
    simpl. rewrite -> rev_snoc. rewrite -> IHl. reflexivity.
Qed.

Lemma snoc_rev: forall {X : Type} (x:X) (l1 l2 : list X),
    snoc (l1 ++ l2) x = l1 ++ (snoc l2 x).
Proof.
    intros X x l1 l2. induction l1.
    simpl. reflexivity.
    simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma rev_distributive: forall {X : Type} (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros X l1 l2. induction l1 as [| x l1'].
    Case "l1 = nil".
        simpl. rewrite -> app_nil_end. reflexivity.
    Case "l1 = x :: l1'".
        simpl. rewrite -> IHl1'. rewrite -> snoc_rev.
        reflexivity.
Qed.

Theorem pal_thm2: forall {X : Type} (l: list X),
    pal l -> l = rev l.
Proof.
    intros X l H. induction H.
    Case "pal_nil".
        simpl. reflexivity.
    Case "pal_singl".
        simpl. reflexivity.
    Case "pal_sum".
        remember (l ++ [x]) as l'.
        simpl. rewrite -> snoc_append.
        rewrite -> Heql'. rewrite -> rev_distributive.
        simpl. rewrite <- IHpal.
        reflexivity.
Qed. 

    
Theorem pal_thm3: forall {X : Type} (l : list X),
    l = rev l -> pal l.
Proof.
    intros X l H. induction l as [| x l'].
    Case "nil".
       apply pal_nil.
    Case "cons".
       simpl in H. rewrite -> H. rewrite -> snoc_append.
       remember (rev l') as l''. destruct l''.
       SCase "nil".
           simpl. apply (pal_singl x).
       SCase "cons".
           inversion H. rewrite <- H1. simpl.
           apply (pal_sum x l'').
Admitted.

Inductive subseq: list nat -> list nat -> Prop :=
| subseq_nil : forall l:list nat, subseq nil l
| subseq_add : forall (s l : list nat) (n:nat),
                 subseq s l -> subseq (n::s) (n::l)
| subseq_pad : forall (s l : list nat) (n:nat),
                 subseq s l -> subseq s (n::l).

Theorem subseq_refl: forall l:list nat,
    subseq l l.
Proof.
    intro l. induction l.
    Case "nil". apply (subseq_nil).
    Case "cons". apply (subseq_add). apply IHl.
Qed.

Lemma subseq_trans_app_helper: forall (l1 l2 : list nat) (x:nat),
    l1 ++ x :: l2 = l1 ++ [x] ++ l2.
Proof.
    intros l1 l2 x. simpl. reflexivity.
Qed.

Lemma subseq_app_end: forall (l1 l2 : list nat) (x:nat),
    subseq l1 l2 -> subseq l1 (l2 ++ [x]).
Proof.
    intros l1 l2 x Eq. induction Eq.
    apply subseq_nil.
    simpl. apply subseq_add. apply IHEq.
    simpl. apply subseq_pad. apply IHEq.
Qed.

Theorem subseq_trans_app: forall l1 l2 l3 : list nat,
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
    intros l1 l2 l3 Eq. generalize dependent l2.
    induction l3 as [| x l3'].
    Case "nil".
        intros l2 Eq. rewrite -> app_nil_end.  apply Eq.
    Case "cons".
        intros l2 Eq. rewrite -> subseq_trans_app_helper.
        rewrite <- app_assoc. remember (l2 ++ [x]) as l2'.
        apply IHl3'. rewrite -> Heql2'.  inversion Eq.
        apply subseq_nil.
        simpl. apply subseq_add. apply subseq_app_end. apply H.
        simpl. apply subseq_pad. apply subseq_app_end. apply H.
Qed.

