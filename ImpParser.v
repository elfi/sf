Require Import SfLib.
Require Imp.

Require Import String.
Require Import Ascii.

Open Scope list_scope.

Definition isWhite (c : ascii) : bool :=
    let n := nat_of_ascii c in
    orb (orb (beq_nat n 32)   (* space *)
             (beq_nat n 9))   (* tab *)
        (orb (beq_nat n 10)   (* linefeed *)
             (beq_nat n 13)). (* cr *)

Notation "x '<=?' y" := (ble_nat x y)
    (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
    let n := nat_of_ascii c in
        andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
    let n := nat_of_ascii c in
        orb (andb (65 <=? n) (n <=? 90))
            (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
    let n := nat_of_ascii c in
        andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
    if isWhite c then white
    else if isAlpha c then alpha
    else if isDigit c then digit
    else other.

Fixpoint list_of_string (s : string) : list ascii :=
    match s with
    | EmptyString => []
    | String c s => c :: (list_of_string s)
    end.

Fixpoint string_of_list (xs : list ascii) : string :=
    fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
    : list (list ascii) :=
    let tk := match acc with
        | [] => []
        | _::_ => [rev acc]
        end
    in
    match xs with
    | [] => tk
    | (x :: xs') =>
      match cls, classifyChar x, x with
      | _,_, "("         => tk ++ ["("]::(tokenize_helper other [] xs')
      | _,_, ")"         => tk ++ [")"]::(tokenize_helper other [] xs')
      | _, white , _     => tk ++ (tokenize_helper other [] xs')
      | alpha, alpha, x  => tokenize_helper alpha (x::acc) xs'
      | digit, digit, x  => tokenize_helper digit (x::acc) xs'
      | other, other, x  => tokenize_helper other (x::acc) xs'
      | _, tp, x         => tk ++ (tokenize_helper tp [x] xs')
      end
    end %char.

Definition tokenize (s : string) : list string :=
    map string_of_list (tokenize_helper white [] (list_of_string s)).

Example tokenize_ex1 :
    tokenize "abc12==3  223*(3+(a+c))" %string
  = ["abc"; "12"; "=="; "3"; "223";
     "*"; "("; "3"; "+"; "(";
     "a"; "+"; "c"; ")"; ")"] %string.
Proof. reflexivity. Qed.

Inductive optionE (X:Type) : Type :=
| SomeE : X -> optionE X
| NoneE : string -> optionE X.

Implicit Arguments SomeE [[X]].
Implicit Arguments NoneE [[X]].

Notation "'DO' ( x , y ) <-- e1 ; e2 'OR' e3"
   := (match e1 with
         | SomeE (x,y) => e2
         | NoneE err => e3
       end)
   (right associativity, at level 60, e2 at next level).

Notation "'DO' (x , y ) <== e1 ; e2"
    := (match e1 with
        | SomeE (x,y) => e2
        | NoneE err => NoneE err
        end)
    (right associativity, at level 60).


