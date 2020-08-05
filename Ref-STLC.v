Require Import String.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.ListSet.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Coq.FSets.FMapWeakList.
Module FM := Coq.FSets.FMapWeakList.
Require Coq.FSets.FMapFacts.
Module FF := Coq.FSets.FMapFacts.
Require Import Coq.Arith.PeanoNat.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.

Inductive type : Type :=
    | TUnit
    | TFun : type -> type -> type
    | TRef : type -> type.

Fixpoint type_eqb (a b : type) : bool :=
    match a, b with
    | TUnit, TUnit => true 
    | TFun a1 a2, TFun b1 b2 => type_eqb a1 b1 && type_eqb a2 b2
    | TRef a, TRef b => type_eqb a b
    | _, _ => false
    end.

Definition id := string.

Definition loc := nat.

Inductive expr : Type :=
    | EVar : id -> expr
    | EFun : id -> type -> expr -> expr
    | EApp : expr -> expr -> expr
    | EUnit
    | ERef : expr -> expr
    | EBang : expr -> expr
    | EAss : expr -> expr -> expr
    | ELoc : loc -> expr.

Inductive value : expr -> Prop :=
    | vfun : forall (x : id) (t : type) (e : expr),
        value (EFun x t e)
    | vunit : value EUnit
    | vloc : forall (l : loc), 
        value (ELoc l).

Module IdDec <: SE.DecidableType.
    Import SE.
    Require Import RelationClasses.
    Definition t := id.
    Definition eq (x1 x2 : t) := x1 = x2.
    Declare Instance eq_equiv : Equivalence eq.
    Theorem eq_dec : forall (x1 x2 : t),
        {x1 = x2} + {x1 <> x2}.
    Proof. intros. apply string_dec. Qed.
    Theorem eq_refl : forall (x : t), x = x.
    Proof. intros. reflexivity. Qed.
    Theorem eq_sym : forall (x y : t), x = y -> y = x.
    Proof. unfold eq. intros; subst; reflexivity. Qed.
    Theorem eq_trans : forall (x y z : t), x = y -> y = z -> x = z.
    Proof. intros; subst. reflexivity. Qed.
End IdDec.

Module IM := FM.Make(IdDec).

Module IFF := FF.WFacts_fun(IdDec)(IM).

(* typing context *)
Definition gamma := IM.t type.

Module LocDec <: SE.DecidableType.
    Import SE.
    Require Import RelationClasses.
    Definition t := loc.
    Definition eq (l1 l2 : t) := l1 = l2.
    Declare Instance eq_equiv : Equivalence eq.
    Theorem eq_dec : forall (l1 l2 : t),
        {l1 = l2} + {l1 <> l2}.
    Proof. intros. apply Nat.eq_dec. Qed.
    Theorem eq_refl : forall (l : t), l = l.
    Proof. intros. reflexivity. Qed.
    Theorem eq_sym : forall (l1 l2 : t), l1 = l2 -> l2 = l1.
    Proof. unfold eq. intros; subst; reflexivity. Qed.
    Theorem eq_trans : forall (l1 l2 l3 : t), l1 = l2 -> l2 = l3 -> l1 = l3.
    Proof. intros; subst. reflexivity. Qed.
End LocDec.

Module LM := FM.Make(LocDec).

Module LF := FF.WFacts_fun(LocDec)(LM).

(* evaluation stores *)
Definition mu : Type := LM.t expr.

(* typing stores *)
Definition sigma : Type := LM.t type.

(* Static Semantics *)
Inductive check (g : gamma) (s : sigma) : expr -> type -> Prop :=
    | check_var : forall (x : id) (t : type), 
        IM.MapsTo x t g ->
        check g s (EVar x) t
    | check_fun : forall (x : id) (t t' : type) (e : expr),
        check (IM.add x t g) s e t' ->
        check g s (EFun x t e) (TFun t t')
    | check_app : forall (e1 e2 : expr) (t t' : type),
        check g s e1 (TFun t t') ->
        check g s e2 t ->
        check g s (EApp e1 e2) t'
    | check_unit : check g s EUnit TUnit
    | check_ref : forall (e : expr) (t : type),
        check g s e t ->
        check g s (ERef e) (TRef t)
    | check_bang : forall (e : expr) (t : type),
        check g s e (TRef t) ->
        check g s (EBang e) t
    | check_ass : forall (e1 e2 : expr) (t : type),
        check g s e1 (TRef t) ->
        check g s e2 t ->
        check g s (EAss e1 e2) TUnit
    | check_loc : forall (l : loc) (t : type),
        LM.find l s = Some t ->
        check g s (ELoc l) (TRef t).

(* variable sets *)
Module IS := WS.Make(IdDec).

(* free variables of an expression *)
Fixpoint fv (e : expr) : IS.t :=
    match e with
    | EVar x => IS.singleton x
    | EFun x _ e => IS.remove x (fv e)
    | EApp e1 e2 => IS.union (fv e1) (fv e2)
    | EUnit => IS.empty
    | ERef e => fv e
    | EBang e => fv e
    | EAss e1 e2 => IS.union (fv e1) (fv e2)
    | ELoc _ => IS.empty
    end.

(* Capture-avoiding Substitution *)
Inductive sub (x : id) (es : expr) : expr -> expr -> Prop :=
    | sub_hit : sub x es (EVar x) es
    | misssub : forall (y : id), 
        x <> y -> 
        sub x es (EVar y) (EVar y)
    | sub_fun_bound : forall (t : type) (e : expr),
        sub x es (EFun x t e) (EFun x t e)
    | sub_lam_notfree : forall (y : string) (t : type) (e e' : expr),
        x <> y ->
         ~ IS.In y (fv es) -> 
        sub x es e e' -> 
        sub x es (EFun y t e) (EFun y t e')
    | sub_lam_free : forall (y z : id) (t : type) (e e' e'' : expr),
        x <> y -> 
        x <> z -> 
        y <> z ->
        IS.In y (fv es) -> 
        ~ IS.In z (fv es) ->
        ~ IS.In z (fv e) ->
        sub y (EVar z) e e' -> 
        sub x es e' e'' -> 
        sub x es (EFun y t e) (EFun z t e'')
    | sub_app : forall (e1 e1' e2 e2' : expr),
        sub x es e1 e1' -> 
        sub x es e2 e2' -> 
        sub x es (EApp e1 e2) (EApp e1' e2')
    | sub_unit : sub x es EUnit EUnit
    | sub_ref : forall (e e' : expr),
        sub x es e e' ->
        sub x es (ERef e) (ERef e')
    | sub_bang : forall (e e' : expr),
        sub x es e e' ->
        sub x es (EBang e) (EBang e')
    | sub_ass : forall (e1 e1' e2 e2' : expr),
        sub x es e1 e1' ->
        sub x es e2 e2' ->
        sub x es (EAss e1 e2) (EAss e1' e2')
    | sub_loc : forall (l : loc),
        sub x es (ELoc l) (ELoc l).

Axiom sub_exists : forall (x : string) (es e : expr), exists e', sub x es e e'.

(* Dynamic Semantics *)
Inductive step (m : mu) : expr -> expr -> mu -> Prop :=
    | step_redux : forall (x : id) (t : type) (e1 e2 e3 : expr),
        sub x e2 e1 e3 -> 
        step m (EApp (EFun x t e1) e2) e3 m
    | step_app : forall (e1 e1' e2 : expr) (m' : mu),
        step m e1 e1' m' -> 
        step m (EApp e1 e2) (EApp e1' e2) m'
    | step_ref : forall (l : loc) (e : expr),
        ~ LM.In l m ->
        step m (ERef e) (ELoc l) (LM.add l e m)
    | step_loc : forall (l : loc) (e : expr),
        LM.MapsTo l e m ->
        step m (EBang (ELoc l)) e m
    | step_bang : forall (e e' : expr) (m' : mu),
        step m e e' m' ->
        step m (EBang e) (EBang e') m'
    | step_ass1 : forall (l : loc) (e : expr),
        step m (EAss (ELoc l) e) EUnit (LM.add l e m)
    | step_ass2 : forall (e1 e1' e2 : expr) (m' : mu),
        step m e1 e1' m' ->
        step m (EAss e1 e2) (EAss e1' e2) m'.

Definition subset (s s' : sigma) :=
    forall (l : loc) (t : type), LM.MapsTo l t s -> LM.MapsTo l t s'.

Lemma mu_monotonic :
    forall (g : gamma) (s s' : sigma) (e : expr) (t : type),
    check g s e t -> subset s s' -> check g s' e t.
Proof.
    intros. dependent induction H;
    try constructor; try assumption; auto.
    - eapply check_app; auto.
    - eapply check_ass; auto.
    - eapply LF.find_mapsto_iff. apply H0. 
        eapply LF.find_mapsto_iff. assumption.
Qed.

Definition dom_eq {A B : Type} (fa : LM.t A) (fb : LM.t B) : Prop :=
    forall (l : loc), LM.In l fa <-> LM.In l fb.

Definition well_typed_ctxts (m : mu) (s : sigma) (g : gamma) : Prop :=
    dom_eq m s /\ forall (l : loc) (e : expr) (t : type), 
        LM.MapsTo l e m ->
        LM.MapsTo l t s ->
        check g s e t.

Definition preservation 
    (g : gamma) (s : sigma) (e e' : expr) (m m' : mu) (t : type) : Prop := 
    step m e e' m' ->
    well_typed_ctxts m s g ->
    check g s e t ->
    forall (s' : sigma), subset s s' ->
    well_typed_ctxts m' s' g /\ check g s' e' t.

Definition substitution_lemma 
    (x : id) (e1 e1' e2 : expr) : Prop := 
    sub x e2 e1 e1' ->
    forall (g : gamma) (s : sigma) (a b : type),
    check (IM.add x a g) s e1 b -> 
    check g s e2 a ->
    check g s e1' b.

Axiom add_twice : 
    forall {T : Type} (x : id) (a b : T) (map : IM.t T),
    IM.add x a (IM.add x b map) = IM.add x a map.

Theorem substitution_lemma_holds : 
    forall (x : id) (e1 e1' e2 : expr),
    substitution_lemma x e1 e1' e2.
Proof.
    unfold substitution_lemma.
    intros x e1 e1' e2 HS.
    induction HS; intros.
    - inversion H; subst.
        apply IFF.add_mapsto_iff in H2 as [[_ AB] | [HMT _]]; 
        subst; auto. contradiction.
    - inversion H0; subst. constructor. eapply IM.add_3 in H.
        + apply H.
        + apply H3.
    - inversion H; subst. constructor. 
        rewrite add_twice in H5. assumption.
    - inversion H1; subst. constructor.
        specialize IHHS with 
            (g := g) (s := s) (a := a) (b := t').
            admit.
    - inversion H5; subst. admit.
    - inversion H; subst. eapply check_app.
        + eapply IHHS1.
            * apply H3.
            * assumption.
        + eapply IHHS2.
            * apply H5.
            * assumption.
    - inversion H; subst. constructor.
    - inversion H; subst. 
        constructor. eapply IHHS.
        + apply H2.
        + assumption.
    - inversion H; subst.
        constructor. eapply IHHS.
        + apply H2.
        + assumption.
    - inversion H; subst.
        eapply check_ass.
        + eapply IHHS1.
            * apply H3.
            * assumption.
        + eapply IHHS2.
            * apply H5.
            * assumption.
    - inversion H; subst.
        constructor. assumption.
Admitted.





