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

