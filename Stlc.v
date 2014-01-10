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
Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).

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

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T t v,
        value v ->
        (tapp (tabs x T t) v) ==> [x:=v]t
| ST_App1 : forall t1 t1' t2,
        t1 ==> t1' ->
        tapp t1 t2 ==> tapp t1' t2
| ST_App2 : forall v t2 t2',
        value v ->
        t2 ==> t2' ->
        tapp v t2 ==> tapp v t2'
| ST_IfTrue : forall t1 t2,
        (tif ttrue t1 t2) ==> t1
| ST_IfFalse : forall t1 t2,
        (tif tfalse t1 t2) ==> t2
| ST_If : forall t1 t1' t2 t3,
        t1 ==> t1' ->
        (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
    | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue"
    | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Lemma step_example1:
    (tapp idBB idB) ==>* idB.
Proof.
    eapply multi_step.
      apply ST_AppAbs. apply v_abs.
      simpl. apply multi_refl.
Qed.

Lemma step_example2:
    (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
    eapply multi_step.
        apply ST_App2.
            apply v_abs.
            apply ST_AppAbs. apply v_abs.
        simpl. eapply multi_step.
            apply ST_AppAbs. apply v_abs.
            simpl. apply multi_refl.
Qed.

Lemma step_example3:
    tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof.
    eapply multi_step; auto.
    simpl. eapply multi_step; auto.
    simpl. eapply multi_step; auto.
Qed.

Lemma step_example4:
    tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof.
    eapply multi_step. auto.
    simpl. eapply multi_step. auto.
    simpl. eapply multi_step. auto.
    simpl. apply multi_refl.
Qed.


Lemma step_example1':
    (tapp idBB idB) ==>* idB.
Proof. normalize. Qed.

Lemma step_example2':
    (tapp idBB (tapp idBB idB)) ==>* idB.
Proof. normalize. Qed.

Lemma step_example3':
    tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. normalize. Qed.

Lemma step_example4':
    tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. normalize. Qed.

Lemma step_example5:
    (tapp (tapp idBBBB idBB) idB) ==>* idB.
Proof.
    eapply multi_step. auto.
    simpl. eapply multi_step. auto.
    simpl. apply multi_refl.
Qed.

Lemma step_example5':
    (tapp (tapp idBBBB idBB) idB) ==>* idB.
Proof. normalize. Qed.

Module PartialMap.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None).

Definition extend {A:Type} (Gamma : partial_map A)
    (x:id) (T:A) :=
    fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
    (extend ctxt x T) x = Some T.
Proof.
    intros. unfold extend. rewrite -> eq_id. reflexivity.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
    x2 <> x1 ->
    (extend ctxt x2 T) x1 = ctxt x1.
Proof.
    intros. unfold extend. rewrite -> neq_id.
      reflexivity.
      assumption.
Qed.

End PartialMap.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Gamma x T,
        Gamma x = Some T ->
        Gamma |- tvar x \in T
| T_Abs : forall Gamma x T1 t T2,
        extend Gamma x T1 |- t \in T2 ->
        Gamma |- tabs x T1 t \in TArrow T1 T2
| T_App : forall Gamma tt t1 T1 T2,
        Gamma |- tt \in TArrow T1 T2 ->
        Gamma |- t1 \in T1 ->
        Gamma |- tapp tt t1 \in T2
| T_True : forall Gamma,
        Gamma |- ttrue \in TBool
| T_False: forall Gamma,
        Gamma |- tfalse \in TBool
| T_If : forall Gamma t1 t2 t3 T,
        Gamma |- t1 \in TBool ->
        Gamma |- t2 \in T ->
        Gamma |- t3 \in T ->
        Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
    first;
    [ Case_aux c "T_Var" | Case_aux c "T_Abs"
    | Case_aux c "T_App" | Case_aux c "T_True"
    | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

Example typing_example_1 :
    empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
    apply T_Abs. apply T_Var. reflexivity.
Qed.

Example typing_example_1' :
    empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof. auto. Qed.




