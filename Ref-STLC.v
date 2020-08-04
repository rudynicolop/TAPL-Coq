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
Require Import Coq.Arith.PeanoNat.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.

Inductive type : Type :=
    | TUnit
    | TFun : type -> type -> type
    | TRef : type -> type.

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

(* evaluation stores *)
Definition mu : Type := LM.t expr.

(* typing stores *)
Definition sigma : Type := LM.t type.

(* Static Semantics *)
Inductive check (g : gamma) (s : sigma) : expr -> type -> Prop :=
    | check_var : forall (x : id) (t : type), 
        IM.find x g = Some t ->
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
Inductive sub (x : id) (s : expr) : expr -> expr -> Prop :=
    | sub_hit : sub x s (EVar x) s
    | misssub : forall (y : id), 
        y <> x -> 
        sub x s (EVar y) (EVar y)
    | sub_fun_bound : forall (t : type) (e : expr),
        sub x s (EFun x t e) (EFun x t e)
    | sub_lam_notfree : forall (y : string) (t : type) (e e' : expr),
        x <> y ->
         ~ IS.In y (fv s) -> 
        sub x s e e' -> 
        sub x s (EFun y t e) (EFun y t e')
    | sub_lam_free : forall (y z : id) (t : type) (e e' e'' : expr),
        x <> y -> 
        x <> z -> 
        y <> z ->
        IS.In y (fv s) -> 
        ~ IS.In z (fv s) ->
        ~ IS.In z (fv e) ->
        sub y (EVar z) e e' -> 
        sub x s e' e'' -> 
        sub x s (EFun y t e) (EFun z t e'')
    | sub_app : forall (e1 e1' e2 e2' : expr),
        sub x s e1 e1' -> 
        sub x s e2 e2' -> 
        sub x s (EApp e1 e2) (EApp e1' e2')
    | sub_unit : sub x s EUnit EUnit
    | sub_ref : forall (e e' : expr),
        sub x s e e' ->
        sub x s (ERef e) (ERef e')
    | sub_bang : forall (e e' : expr),
        sub x s e e' ->
        sub x s (EBang e) (EBang e')
    | sub_ass : forall (e1 e1' e2 e2' : expr),
        sub x s e1 e1' ->
        sub x s e2 e2' ->
        sub x s (EAss e1 e2) (EAss e1' e2')
    | sub_loc : forall (l : loc),
        sub x s (ELoc l) (ELoc l).

Axiom sub_exists : forall (x : string) (s e : expr), exists e', sub x s e e'.

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
        LM.find l m = Some e ->
        step m (EBang (ELoc l)) e m
    | step_bang : forall (e e' : expr) (m' : mu),
        step m e e' m' ->
        step m (EBang e) (EBang e') m'
    | step_ass1 : forall (l : loc) (e : expr),
        step m (EAss (ELoc l) e) EUnit (LM.add l e m)
    | step_ass2 : forall (e1 e1' e2 : expr) (m' : mu),
        step m e1 e1' m' ->
        step m (EAss e1 e2) (EAss e1' e2) m'.