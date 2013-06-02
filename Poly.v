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

Module MumbleBaz.

Inductive mumble : Type :=
| a : mumble
| b : mumble -> nat -> mumble
| c : mumble.

Inductive grumble (X:Type) : Type :=
| d : mumble -> grumble X
| e : X -> grumble X.

(* Check (d (b a 5)).
   (b a 5) has type mumble instead of Type *)
Check (d mumble (b a 5)). (* grumble mumble*)
Check (d bool (b a 5)).   (* grumble bool *)
Check (e bool true).      (* grumble bool *)
Check (e mumble (b c 0)). (* grumble mumble *)
(* Check (e bool (b c 0)). 
   (b c 0)  has type mumble instead of bool *)
(* Check c.
   type mumble, not grumble X *)

Inductive baz: Type :=
| x : baz -> baz
| y : baz -> bool -> baz.

(* baz has no elements, it cannot be constructed *)

End MumbleBaz.

Fixpoint app' X l1 l2 : list X :=
    match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
    end.

Check app'.
Check app.

Fixpoint length' (X : Type) (l : list X) : nat :=
    match l with
    | nil => 0
    | cons h t => S (length' _ t)
    end.

Definition list123 :=
    cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

Fixpoint length'' {X : Type} (l : list X) : nat :=
    match l with
    | nil => 0
    | cons h t => S (length'' t)
    end.

Definition mynil : list nat := nil.

Check nil. (* nil : list ?64 *)
Check @nil. (* @nil : forall X : Type, list X *)

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1, 2, 3].

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
    match count with
    | O => nil
    | S count' => n :: (repeat X n count')
    end.

Example test_repeat1:
    repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app: forall X:Type, forall l:list X,
    app [] l = l.
Proof.
    intros X l. simpl. reflexivity.
Qed.

Theorem rev_snoc: forall X : Type,
                  forall v : X,
                  forall s : list X,
    rev (snoc s v) = v :: (rev s).
Proof.
    intros X v s. induction s as [| x xs].
    Case "s = nil".
        simpl. reflexivity.
    Case "s = cons x xs".
        simpl. rewrite -> IHxs. simpl. reflexivity.
Qed.

Theorem rev_involutive: forall X:Type, forall l:list X,
    rev (rev l) = l.
Proof.
    intros X l. induction l as [| x xs].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = cons x xs".
        simpl. rewrite -> rev_snoc. rewrite -> IHxs.
        reflexivity.
Qed.

Theorem snoc_with_append: forall X : Type,
                          forall l1 l2 : list X,
                          forall v : X,
    snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
    intros X l1 l2 v. induction l1 as [| x xs].
    Case "l1 = nil".
        simpl. reflexivity.
    Case "l1 = cons x xs".
        simpl. rewrite -> IHxs. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
    pair : X -> Y -> prod X Y.

Check prod. (* prod : Type -> Type -> Type *)
Check pair. (* pair: forall X Y, X -> Y -> prod X Y *)

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
    match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
    match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
    : list (X*Y) :=
    match (lx, ly) with
    | ([], _) => []
    | (_, []) => []
    | (x::xs, y::ys) => (x, y) :: combine xs ys
    end.

Check combine. (* combine: 
                     list ?215 -> list ?216 -> list (?215 * ?216) *)
Check @combine.  (* combine: 
                      forall X Y : Type, X -> Y -> list (X * Y) *)

Fixpoint split {X Y : Type} (l : list (X * Y))
    : (list X) * (list Y) :=
    match l with
    | nil => (nil, nil) 
    | (x,y) :: tail => ( x :: (fst (split tail)),
                         y :: (snd (split tail)))
    end.

Example test_split:
    split [(1, false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity. Qed.

Inductive option (X : Type) : Type :=
| Some : X -> option X
| None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
    match l with
    | nil => None
    | x :: xs => if beq_nat O n
                 then Some x
                 else index (pred n) xs
    end.

Example test_index1: index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.

Example test_index2: index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.

Example test_index3: index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X : Type} (l : list X) : option X :=
    match l with
    | nil => None
    | x :: xs => Some x
    end.

Check @hd_opt.

Example test_hd_opt1: hd_opt [1,2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_opt2: hd_opt [[1],[2]] = Some [1].
Proof. reflexivity. Qed.

Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
    f (f (f n)).

Check @doit3times.

Example test_doit3times1: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times2: doit3times negb true = false.
Proof. reflexivity. Qed.

Check plus. (* plus : nat -> nat -> nat *)

Definition plus3 := plus 3.
Check plus3. (* plus3 : nat -> nat *)

Example test_plus3: plus3 4 = 7.
Proof. reflexivity. Qed.

Example test_plus3': doit3times plus3 0 = 9.
Proof. reflexivity. Qed.

Example test_plus3'': doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
    (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
    (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry: forall (X Y Z : Type)
                              (f : X -> Y -> Z)
                              (x : X) (y : Y),
    prod_curry (prod_uncurry f) x y = f x y.
Proof. intros X Y Z f x y. reflexivity. Qed.

Theorem curry_uncurry: forall (X Y Z : Type)
                              (f : (X * Y) -> Z)
                              (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof. intros X Y Z f p. destruct p. reflexivity. Qed.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X)
    : list X :=
    match l with
    | nil => nil
    | x :: xs => if test x
                 then x :: (filter test xs)
                 else (filter test xs)
    end.

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
    beq_nat (length l) 1.

Check @length_is_1.

Example test_filter2:
    filter length_is_1
        [ [1,2], [3], [4], [5,6,6], [], [8] ] =
        [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l : list nat) : nat :=
    length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

Example test_anon_fun':
    doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.


Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
        [ [1,2], [3], [4], [5,6,6], [], [8] ] =
        [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l: list nat) : list nat :=
    filter (fun x => andb (negb (ble_nat x 7)) (evenb x)) l.

Example test_filter_even_gt7_1:
    filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2:
    filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X)
    : list X * list X :=
    (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5,9,0] =
                              ([], [5,9,0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
    match l with
    | nil => nil
    | x :: xs => (f x) :: map f xs
    end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.

Example test_map2: map oddb [2,1,2,5] = [false, true, false, true].
Proof. reflexivity. Qed.

Example test_map3: map (fun n => [evenb n,oddb n]) [2,1,2,5]
    = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity. Qed.

Lemma map_snoc: forall (X Y : Type) (f : X -> Y) 
                       (l : list X) (x : X),
    map f (snoc (l) x) = snoc (map f l) (f x).
Proof.
    intros X Y f l x. induction l as [| h t].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = h :: t".
        simpl. rewrite <- IHt. reflexivity.
Qed.

Theorem map_rev: forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
    intros X Y f l. induction l as [| x xs].
    Case "l = nil".
        simpl. reflexivity.
    Case "l = x :: xs".
        simpl. rewrite <- IHxs. rewrite -> map_snoc. reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f:X->list Y) (l:list X)
    : list Y :=
    match l with
    | nil => nil
    | x :: xs => (f x) ++ (flat_map f xs)
    end.

Example test_flat_map1:
    flat_map (fun n => [n,n,n]) [1,5,4] 
    = [1,1,1,5,5,5,4,4,4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
    : option Y :=
    match xo with
    | None => None
    | Some x => Some (f x)
    end.

(* explicit args in filter and map *)
Fixpoint filter' (X : Type) (test : X -> bool) (l : list X)
    : list X :=
    match l with
    | nil => nil
    | x :: xs => if (test x)
                 then x :: (filter' X test xs)
                 else (filter' X test xs)
    end.

Fixpoint map' (X Y : Type) (f : X ->Y) (l : list X)
    : list Y :=
    match l with
    | nil => nil
    | x :: xs => (f x) :: (map' X Y f xs)
    end.

Fixpoint fold {X Y : Type} (f : X ->Y->Y) (l:list X) (b:Y)
    : Y :=
    match l with
    | nil => b
    | x :: xs => f x (fold f xs b)
    end.

Check (fold andb).

Example fold_example1: fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2:
    fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3:
    fold app [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

Definition constfun {X : Type} (x : X) : nat -> X :=
    fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1: ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2: (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X : Type} (f : nat->X) (k:nat) (x:X)
    : nat -> X :=
    fun (k':nat) => if beq_nat k k' then x else (f k').

Definition fmostlytrue :=
    override (override ftrue 1 false) 3 false.

Example override_example1: fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2: fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3: fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4: fmostlytrue 3 = false.
Proof. reflexivity. Qed.

Theorem override_example: forall (b:bool),
    (override (constfun b) 3 true) 2 = b.
Proof.
    intro b. reflexivity.
Qed.

Theorem unfold_example: forall m n,
    3 + n = m ->
    plus3 n + 1 = m + 1.
Proof.
    intros m n H. unfold plus3. rewrite -> H. reflexivity.
Qed.

Theorem override_eq: forall {X:Type} x k (f:nat->X),
    (override f k x) k = x.
Proof.
    intros X x k f. unfold override.
    rewrite <- beq_nat_refl. reflexivity.
Qed.

Theorem override_neq: forall {X:Type} x1 x2 k1 k2 (f:nat->X),
    f k1 = x1 ->
    beq_nat k2 k1 = false ->
    (override f k2 x2) k1 = x1.
Proof.
    intros X x1 x2 k1 k2 f H1 H2.
    unfold override. rewrite -> H2. assumption.
Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
    fold (fun x n => S n) l 0.

Example test_fold_length1: fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct: forall X (l : list X),
    fold_length l = length l.
Proof.
    intros X l. induction l as [| x xs].
    Case "l = nil".
        simpl. unfold fold_length. simpl. reflexivity.
    Case "l = x :: xs".
        simpl. rewrite <- IHxs.
        unfold fold_length. simpl. reflexivity.
Qed.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X)
    : list Y :=
    fold (fun x ys => (f x) :: ys) l nil.

Eval compute in (fold_map S [1,2,3]).

Theorem fold_map_correct: forall (X Y : Type) (f : X->Y) (l : list X),
    fold_map f l = map f l.
Proof.
    intros X Y f l. induction l as [| x xs].
    Case "l = nil".
        simpl. unfold fold_map. simpl. reflexivity.
    Case "l = x :: xs".
        simpl. rewrite <- IHxs.
        unfold fold_map. simpl. reflexivity.
Qed.

Module Church.

(* n:nat defined as a function that takes a function f as
   a parameter and returns f iterated n times:
   n f x = f^n x
*)
Definition nat := forall (X : Type), (X -> X) -> (X -> X).

Definition one : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : nat :=
    fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : nat := @doit3times.

(*
    f^(n+1) x =  f (f^n x)  =  f (n f x)  
*)
Definition succ (n : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Example succ_1: succ zero = one.
Proof. reflexivity. Qed.

Example succ_2: succ one = two.
Proof. reflexivity. Qed.

Example succ_3: succ two = three.
Proof. reflexivity. Qed.

(*
    f^(n+m) x  =  f^n (f^m x)  =  n f (m f x)
*)
Definition plus (n m : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).

Example plus_1: plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2: plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3:
    plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(*
    f^(n*m) x  =  (f^m)^n x  =  n f^m x  =  n (m f) x
*)
Definition mult (n m : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.

Example mult_1: mult one one = one.
Proof. reflexivity. Qed.

Example mult_2: mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3: mult two three = plus three three.
Proof. reflexivity. Qed.

(*
    f^(n^m) x  =  (n^m f) x  =  (m n f) x
*)
Definition exp (n m : nat) : nat :=
    fun (X : Type) (f : X -> X) (x : X) => (m (X->X) (n X) f) x.

Example exp_1: exp two two = plus two two.
Proof. reflexivity. Qed.

Eval compute in (exp three two).

Example exp_2: exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3: exp three zero = one.
Proof. reflexivity. Qed.

End Church.
