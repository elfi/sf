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
