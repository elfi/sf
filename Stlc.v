Require Export Types.

Module STLC.

Inductive ty : Type :=
| TBool : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tvar : id -> tm
| tapp : tm -> tm -> tm
| tabs : id -> ty -> tm -> tm
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "tvar" | Case_aux c "tapp"
    | Case_aux c "tabs" | Case_aux c "ttrue"
    | Case_aux c "tfalse" | Case_aux c "tif" ].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(* idB = \x:Bool . x *)
Notation idB := (tabs x TBool (tvar x)).

(* idBB = \x:(Bool -> Bool) . x *)
Notation idBB := (tabs x (TArrow TBool TBool) (tvar x)).

(* idBBB = \x:(Bool->Bool) -> (Bool -> Bool) . x *)
Notation idBBBB := (tabs x (TArrow (TArrow TBool TBool)
                                   (TArrow TBool TBool)) (tvar x)).
(* k = \x:Bool . \y:Bool . x *)
Notation k := (tabs x TBool (tabs y TBool (tvar))).

(* notB = \x:Bool . if x then false else true *)
Notation notB := (tabs x TBool (tif (tvar x) false true)).

Inductive value : tm -> Prop :=
| v_abs   : forall x T t, value (tabs x T t)
| v_true  : value ttrue
| v_false : value tfalse.

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
    match t with
    | tvar x'      => if eq_id_dec x x' then s else t
    | tabs x' T t1 =>
          tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1))
    | tapp t1 t2   => tapp ([x:=s] t1) ([x:=s] t2)
    | ttrue        => ttrue
    | tfalse       => tfalse
    | tif t1 t2 t3 =>
          tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
    end

where "'[' x ':=' s ']' t" := (subst x s t).


Inductive substi (s:tm) (x:id) : tm -> tm -> Prop :=
| s_var1 : substi s x (tvar x) s
| s_var2 : forall y, x <> y ->
             substi s x (tvar y) (tvar y)
| s_abs1 : forall T t1, substi s x (tabs x T t1) (tabs x T t1)
| s_abs2 : forall y, x <> y ->
           forall t1 t1', substi s x t1 t1' ->
           forall T, substi s x (tabs y T t1) (tabs y T t1')
| s_app  : forall t1 t1' t2 t2',
           substi s x t1 t1' ->
           substi s x t2 t2' ->
           substi s x (tapp t1 t2) (tapp t1' t2')
| s_ttrue : substi s x ttrue ttrue
| s_tfalse : substi s x tfalse tfalse
| s_tif : forall t1 t1' t2 t2' t3 t3',
          substi s x t1 t1' ->
          substi s x t2 t2' ->
          substi s x t3 t3' ->
          substi s x (tif t1 t2 t3) (tif t1' t2' t3').

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
    [x:=s]t = t' <-> substi s x t t'.
Proof.
    split.
    Case "->".
        generalize dependent t'.
        t_cases (induction t) SCase;
            simpl; intros;
               (try (inversion H; clear H));
               (try (destruct (eq_id_dec x0 i)); subst);
               auto.
    Case "<-".
        intro H. induction H; simpl; auto.
        SCase "s_var1".
            auto using eq_id.
        SCase "s_var2".
            auto using neq_id.
        SCase "s_abs1".
            rewrite -> eq_id. reflexivity.
        SCase "s_abs2".
            rewrite -> neq_id.
              rewrite -> IHsubsti. reflexivity.
              assumption.
        SCase "s_app".
            rewrite -> IHsubsti1.
            rewrite -> IHsubsti2.
            reflexivity.
        SCase "s_tif".
            rewrite -> IHsubsti1.
            rewrite -> IHsubsti2.
            rewrite -> IHsubsti3.
            reflexivity.
Qed.


