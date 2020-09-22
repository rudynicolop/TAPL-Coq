Require Import String.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.

(* 
    In Hindley-Milner.v, I defined small
    languages, one with monomorphic
    type inference, and the other with
    polymorphic type inference
    and proved limited results,
    and these results were largely
    unsatisfactory. These endeavors were
    based upon the presentation in
    Types and Programming Languages
    by Benjamin Pierce.

    In this file, I attempt to formalize in Coq
    Luis Damas's and Robin Milner's 
    results in there paper
    Principal type-schemes for functional programs.
    While Pierce's treatment of monorphic inference
    and unification were superb, he only provided
    a sketch of the issues with let-polymorphism.
    Milner's paper provides the following:
    - A simple calculus with let-bindings
    - A type-inference algorithm (Algorithm W)
        that interleaves constraint generation
        and unification (an exercise Pierce
        leaves to the reader, which I attempted)
    - A soundness proof of this algorithm
        (a result I was unable to produce
        with my aforementioned attempt)

    The Language I present omits conditionals
    and recursion, and has a base expression unit.

    I also have avoided denotational semantics
    and opted for a big-step
    operational semantics.
*)

Ltac inv H := inversion H; subst.

Ltac injintrosubst H :=
    injection H; intros; subst.

Definition id := string.

Inductive expr : Type :=
    | EUnit
    | EVar (x : id)
    | EApp (e1 e2 : expr)
    | EFun (x : id) (e : expr)
    | ELet (x : id) (e1 e2 : expr).

Inductive value : Type :=
    VUnit | VFun (x : id) (e : expr).

Section IdMap.
    Context {T : Type}.

    Definition imap : Type := list (id * T).

    Definition iempty : imap := [].

    Definition ibind (x : id) (t : T) (m : imap) : imap := (x, t) :: m.

    Fixpoint iremove (x : id) (m : imap) : imap :=
        match m with
        | [] => []
        | (y,t) :: m =>
            if (y =? x)%string then (iremove x m) else (y,t) :: (iremove x m)
        end.

    Fixpoint iget (X : id) (m : imap) : option T :=
        match m with
        | [] => None
        | (Y,t)::m => if (Y =? X)%string then Some t else iget X m
        end.

    Fixpoint combine (m1 m2 : imap) : imap := m1 ++ m2.
End IdMap.

Definition env : Type := @imap value.

(* 
    Big-step semantics were chosen because:
    - Operational semantics are relatively
        easy to define and prove over in Coq
        as opposed to denotational semantics.
    -  The paper's denotational semantics
        largely resemble a big-step semantics.

    Milner chose eager-evaluation so I have as well.
*)
Inductive eval (n : env) : expr -> value -> Prop :=
    | eval_unit :
        eval n EUnit VUnit
    | eval_var : forall (x : id) (v : value),
        iget x n = Some v ->
        eval n (EVar x) v
    | eval_app : forall (e1 e2 e : expr) (x : id) (v2 v : value),
        eval n e1 (VFun x e) ->
        eval n e2 v2 ->
        eval (ibind x v2 n) e v ->
        eval n (EApp e1 e2) v
    | eval_fun : forall (x : id) (e : expr),
        eval n (EFun x e) (VFun x e)
    | eval_let : forall (x : id) (e1 e2 : expr) (v1 v2 : value),
        eval n e1 v1 ->
        eval (ibind x v1 n) e2 v2 ->
        eval n (ELet x e1 e2) v2.

Inductive type : Type :=
    | TUnit
    | TVar (X : id)
    | TFun (t1 t2 : type).

Inductive poly : Type :=
    | PType (t : type)
    | PForall (X : id) (t : poly).

(* Type without type variables. *)
Inductive monotype : type -> Prop :=
    | mono_unit : monotype TUnit
    | mono_fun : forall (t1 t2 : type),
        monotype t1 ->
        monotype t2 ->
        monotype (TFun t1 t2).

Module TypeSubstitution.
    Definition T : Type := @imap type.

    (* type type substitution. *)
    Fixpoint st (s : T) (t : type) : type :=
        match t with
        | TUnit => TUnit 
        | TVar X =>
            match iget X s with
            | None => TVar X
            | Some t' => t'
            end
        | TFun t1 t2 => TFun (st s t1) (st s t2)
        end.

    (* poly-type type substitution. *)
    Fixpoint sp (s : T) (p : poly) : poly :=
        match p with
        | PType t => PType (st s t)
        | PForall X p =>
            PForall X (sp (iremove X s) p)
        end.
End TypeSubstitution.
Module TS := TypeSubstitution.

Definition gamma : Type := @imap poly.

Module Closed.
    (* Bound type variables. *)
    Definition bound : Type := list id.

    (* No-free type variables in a type *)
    Inductive ct (b : bound) : type -> Prop :=
        | closed_unit : ct b TUnit
        | closed_var : 
            forall (X : id),
            In X b ->
            ct b (TVar X)
        | closed_fun :
            forall (t1 t2 : type),
            ct b t1 ->
            ct b t2 ->
            ct b (TFun t1 t2).

    (* TODO: closed for poly and gamma. *)
End Closed.

