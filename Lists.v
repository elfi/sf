Require Export Induction.

Module NatList.

Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p:natprod) : nat :=
    match p with
    | pair x y => x
    end.

Definition snd (p:natprod) : nat :=
    match p with
    | pair x y => y
    end.

Eval simpl in (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3,5)).

Definition swap_pair (p:natprod) : natprod :=
    match p with
    | (x,y) => (y,x)
    end.

Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)). (* structure exposed *)
Proof.
    reflexivity.
Qed.

Theorem surjective_pairing : forall (p:natprod),
    p = (fst p, snd p).
Proof.
    intro p. destruct p as (m,n). (* or destruct p as [m n] *)
    simpl. reflexivity.
Qed.

Theorem snd_fst_is_swop : forall (p:natprod),
    (snd p, fst p) = swap_pair p.
Proof.
    intro p. destruct p as (m,n).
    simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p:natprod),
    fst (swap_pair p) = snd p.
Proof.
    intro p. destruct p as (m,n).
    simpl. reflexivity.
Qed.

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1,2,3].

Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => nil
    | S count' => n :: (repeat n count')
    end.

Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => 0
    | x :: xs => S (length xs)
    end.

Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | x :: xs => cons x (app xs l2)
    end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity. Qed.

Example test_app2: nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.

Example test_app3: [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
    match l with
    | nil => default
    | x :: xs => x
    end.

Definition tail (l:natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => xs
    end.

Example test_hd1: hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.

Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tail: tail [1,2,3] = [2,3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
    | nil => nil
    | 0 :: tail => nonzeros tail
    | x :: tail => x :: nonzeros tail
    end.

Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => match oddb x with
                 | true => x :: oddmembers xs
                 | false  => oddmembers xs
                 end
    end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat :=
    match l with
    | nil => 0
    | x :: xs => match oddb x with
                 | true => S (countoddmembers xs)
                 | false => countoddmembers xs
                 end
    end.

Example countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.

Example countoddmembers2: countoddmembers [0,2,4] = 0.
Proof. reflexivity. Qed.

Example countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1,l2 with
    | nil, l2 => l2
    | l1, nil => l1
    | x :: xs, y :: ys => x :: y :: alternate xs ys
    end.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. reflexivity. Qed.

Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof. reflexivity. Qed.

Example test_alternate3: alternate [] [20,30] = [20,30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
    | nil => 0
    | x :: xs => match beq_nat x v with
                 | true => S (count v xs)
                 | false => count v xs
                 end
    end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
    app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
    v :: s.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1,4,1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
    match count v s with
    | 0 => false
    | S n' => true
    end.

Example test_member1: member 1 [1,4,1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1,4,1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) :=
    match s with
    | nil => nil
    | x :: xs => match beq_nat x v with
                 | true => xs
                 | false => x :: remove_one v xs
                 end
    end.

Example test_remone_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remone_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remone_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. reflexivity. Qed.

Example test_remone_one4: count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | x :: xs => match beq_nat x v with
                       | true => remove_all v xs
                       | false => x :: remove_all v xs
                       end
    end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,4,1]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
    | nil => true
    | x :: xs => match member x s2 with
                 | true => subset xs (remove_one x s2)
                 | false => false
                 end
    end.

Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
Proof. reflexivity. Qed.

Theorem bag_theorem: forall (v:nat) (s:bag),
    count v (add v s) = S (count v s).
Proof.
    intros v s. destruct v as [| v'].
    Case "v = 0".
        simpl. reflexivity.
    Case "v = S v'".
        simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem nil_app : forall l:natlist,
    nil ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
    pred (length l) = length (tail l).
Proof.
    intro l. destruct l as [| x xs].
    Case "l = nil".
        reflexivity.
    Case "l = cons x xs".
        simpl. reflexivity.
Qed.

Theorem app_ass: forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros l1 l2 l3. induction l1 as [| x xs].
    Case "l1 = nil".
        simpl. reflexivity.
    Case "l1 = cons x xs".
        simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem app_length: forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    intros l1 l2. induction l1 as [| x xs].
    Case "l1 = nil".
        simpl. reflexivity.
    Case "l1 = cons x xs".
        simpl. rewrite -> IHxs. reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
    match l with
    | nil => [v]
    | x :: xs => x :: (snoc xs v)
    end.

Fixpoint rev (l:natlist) : natlist :=
    match l with
    | nil => nil
    | x :: xs => snoc (rev xs) x
    end.

Example test_rev1: rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem length_snoc: forall n:nat, forall l:natlist,
    length (snoc l n) = S (length l).
Proof.
    intros n l. induction l as [| x xs].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = cons x xs".
        simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem rev_length: forall l:natlist,
    length (rev l) = length l.
Proof.
    intro l. induction l as [| x xs].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = cons x xs".
        simpl. rewrite -> length_snoc. rewrite -> IHxs. reflexivity.
Qed.

Theorem app_nil_end: forall l:natlist,
    l ++ nil = l.
Proof.
    intro l. induction l as [| x xs].
    Case "l = nil".
        reflexivity.
    Case "l = cons x xs".
        simpl. rewrite -> IHxs. reflexivity.
Qed.

Lemma rev_snoc: forall x:nat, forall l:natlist,
    rev (snoc l x) = x :: rev l.
Proof.
    intros n l. induction l as [| x xs].
    reflexivity.
    simpl. rewrite -> IHxs. simpl. reflexivity.
Qed.

Theorem rev_involutive: forall l:natlist,
    rev (rev l) = l.
Proof.
    intro l. induction l as [| x xs].
    Case "l = nil".
        reflexivity.
    Case "l = cons x xs".
        simpl. rewrite -> rev_snoc. rewrite -> IHxs. reflexivity.
Qed.

Theorem app_ass4: forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
    intros l1 l2 l3 l4.
    rewrite -> app_ass. rewrite <- app_ass. reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
    snoc l n = l ++ [n].
Proof.
    intros l n. induction l as [| x xs].
    Case "l = nil".
        reflexivity.
    Case "l = cons x xs".
        simpl. rewrite -> IHxs. reflexivity.
Qed.

Lemma snoc_rev: forall (l1 l2 : natlist) (n : nat),
    snoc (l1 ++ l2) n = l1 ++ (snoc l2 n).
Proof.
    intros l1 l2 n. induction l1 as [| x xs].
    Case "l1 = nil".
        reflexivity.
    Case "l1 = cons x xs".
        simpl.  rewrite -> IHxs. reflexivity.
Qed.

Theorem distr_rev: forall l1 l2 : natlist,
    rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
    intros l1 l2. induction l1 as [| x xs].
    Case "l = nil".
        simpl. rewrite -> app_nil_end. reflexivity.
    Case "l = cons x xs".
        simpl. rewrite -> IHxs. rewrite -> snoc_rev. reflexivity.
Qed.

Lemma nonzeros_app: forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    intros l1 l2. induction l1 as [| x xs].
    Case "l1 = nil".
        reflexivity.
    Case "l1 = cons x xs".
        destruct x as [| x'].
        SCase "x = 0.".
            simpl. rewrite -> IHxs. reflexivity.
        SCase "x = S x'".
            simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem design: forall (l : natlist) (x y : nat),
    x :: (snoc l y) = [x] ++ l ++ [y].
Proof.
    intros l x y. destruct l as [| h hs].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = cons h hs".
        simpl. rewrite -> snoc_append. reflexivity.
Qed.

Theorem count_member_nonzero: forall s : bag,
    ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
    intro s. simpl. reflexivity.
Qed.

Theorem ble_n_Sn: forall n,
    ble_nat n (S n) = true.
Proof.
    intro n. induction n as [| n'].
    Case "n = 0".
        reflexivity.
    Case "n = S n'".
        simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem remove_decrease_count: forall s : bag,
    ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
    intro s. induction s as [| x xs].
    Case "s = nil".
        simpl. reflexivity.
    Case "s = cons x xs".
        destruct x as [| x'].
        SCase "x = 0".
            simpl. rewrite -> ble_n_Sn. reflexivity.
        SCase "x = S x'".
            simpl. rewrite -> IHxs. reflexivity.
Qed.

Theorem bag_count_sum: forall (n : nat) (l1 l2 : natlist),
    count n (sum l1 l2) = (count n l1) + (count n l2).
Proof.
    intros n l1 l2. induction l1 as [| x xs].
    Case "l1 = nil".
        simpl. reflexivity.
    Case "l2 = cons x xs".
        simpl. (* don't know how to consider
    beq_nat x n = true/false cases separately *)
Admitted.

Theorem rev_injective: forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof. Admitted.

Inductive natoption : Type :=
| Some : nat -> natoption
| None : natoption.

Fixpoint index (n:nat) (l:natlist) : natoption :=
    match l with
    | nil => None
    | x :: xs => match n with
                 | 0 => Some x
                 | S n' => index n' xs
                 end
    end.

Example test_index1: index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.

Example test_index2: index 3 [4,5,6,7] = Some 7.
Proof. reflexivity. Qed.

Example test_index3: index 10 [4,5,6,7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n:nat) (l:natlist) : natoption :=
    match l with
    | nil => None
    | x :: xs => if beq_nat n 0
                 then Some x
                 else index' (pred n) xs
    end.

Definition option_elim (d:nat) (o:natoption) : nat :=
    match o with
    | None => d
    | Some x => x
    end.

Definition hd_opt (l:natlist) : natoption :=
    match l with
    | nil => None
    | x :: xs => Some x
    end.

Example test_hd_opt1: hd_opt [] = None.
Proof. reflexivity. Qed.

Example test_hd_opt2: hd_opt [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt3: hd_opt [5,6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd: forall (l:natlist) (default:nat),
    hd default l = option_elim default (hd_opt l).
Proof.
    intros l default. destruct l as [| x xs].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = cons x xs".
        simpl. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | nil, nil => true
    | x :: xs, y :: ys => if beq_nat x y
                          then beq_natlist xs ys
                          else false
    | _, _ => false
    end.

Example test_beq_natlist1: (beq_natlist nil nil) = true.
Proof. reflexivity. Qed.

Example test_beq_natlist2: (beq_natlist [1,2,3] [1,2,3]) = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3: (beq_natlist [1,2,3] [1,2,4]) = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl: forall l:natlist,
    true = beq_natlist l l.
Proof.
    intro l. induction l as [| x xs].
    Case "l = nil".
        reflexivity.
    Case "l = cons x xs".
        simpl. rewrite <- beq_nat_refl. rewrite <- IHxs. reflexivity.
Qed.

Module Dictionary.

Inductive dictionary : Type :=
| empty : dictionary
| record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) : dictionary :=
    (record key value d).

Fixpoint find (key : nat) (d : dictionary) : natoption :=
    match d with
    | empty => None
    | record k v d' => if beq_nat k key
                       then Some v
                       else find key d'
    end.

Theorem dictionary_invarian1' : forall (d : dictionary) (k v : nat),
    (find k (insert k v d)) = Some v.
Proof.
    intros d k v. destruct d as [| k' v' d'].
    Case "d = empty".
        simpl. rewrite <- beq_nat_refl. reflexivity.
    Case "d = record k' v' d'".
        simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem dictionary_invariant2' : forall (d : dictionary) (m n o : nat),
    (beq_nat n m) = false -> (find m d) = (find m (insert n o d)).
Proof.
    intros d m n o H. destruct d as [| k' v' d'].
    Case "d = empty".
        simpl. rewrite -> H. reflexivity.
    Case "d = record k' v' d'".
        simpl. rewrite -> H. reflexivity.
Qed.

End Dictionary.

End NatList.
