Require Import String.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.
Require Coq.MSets.MSetProperties.
Module MSP := Coq.MSets.MSetProperties.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Import Coq.Logic.Decidable.
Require Import Coq.Program.Equality.

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

(* variable sets *)
Module IS := WS.Make(IdDec).
Module ISF := MSF.WFactsOn(IdDec)(IS).
Module ISP := MSP.WPropertiesOn(IdDec)(IS).

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

Definition gamma : Type := @imap poly.

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

    Lemma st_empty :
        forall (t : type), st iempty t = t.
    Proof.
        intros t. induction t; try reflexivity.
        simpl. rewrite IHt1. rewrite IHt2. reflexivity.
    Qed.

    (* iget x (compose m1 m2) ~ m2(m1(x)) *)
    Fixpoint compose (s1 s2 : T) : T :=
        match s1 with
        | [] => s2
        | (X, T) :: s1 => (X, st s2 T) :: compose s1 s2
        end.

    Lemma compose_empty :
        forall (s : T), compose s [] = s.
    Proof.
        induction s; try reflexivity.
        simpl. destruct a as [X T].
        rewrite IHs. rewrite st_empty.
        reflexivity.
    Qed.

    Lemma st_compose :
        forall (s1 s2 : T) (t : type),
        st (compose s1 s2) t = st s2 (st s1 t).
    Proof.
        intros s1 s2. induction t; 
        simpl in *; auto.
        - induction s1; auto; simpl.
            destruct a as [Y T]. simpl.
            destruct (Y =? X) eqn:eq; auto.
        - rewrite IHt1. rewrite IHt2.
            reflexivity.
    Qed.

    (* poly-type type substitution. *)
    Fixpoint sp (s : T) (p : poly) : poly :=
        match p with
        | PType t => PType (st s t)
        | PForall X p =>
            PForall X (sp (iremove X s) p)
        end.

    Lemma sp_empty :
        forall (p : poly), sp iempty p = p.
    Proof.
        induction p; simpl in *.
        - rewrite st_empty. reflexivity.
        - unfold iempty in IHp. rewrite IHp.
            reflexivity.
    Qed.

    Lemma sp_compose :
        forall (s1 s2 : T) (p :poly),
        sp (compose s1 s2) p = sp s2 (sp s1 p).
    Proof.
        intros s1 s2 p.
        generalize dependent s2.
        generalize dependent s1.
        induction p; intros s1 s2;
        simpl in *.
        - rewrite st_compose. reflexivity.
        - induction s1.
            + rewrite sp_empty.
                reflexivity.
            + destruct a as [Y U]. simpl.
                destruct (Y =? X) eqn:eq; auto.
                injection IHs1 as IH.
                rewrite <- IHp. simpl.
    Admitted.

    (* gamma type substitution *)
    Definition sg (s : T) : gamma -> gamma :=
        map (fun xp : id * poly =>
                let (x,p) := xp in
                (x, sp s p)).

    Lemma sg_empty :
        forall (g : gamma), sg [] g = g.
    Proof.
        induction g; simpl; auto.
        destruct a as [X P].
        rewrite sp_empty.
        rewrite IHg. reflexivity.
    Qed.

    Lemma sg_get :
        forall (x : id) (g : gamma) (p : poly),
        iget x g = Some p ->
        forall (S : T),
        iget x (sg S g) = Some (sp S p).
    Proof.
        intros x. induction g;
        intros p HG S;
        try discriminate.
        destruct S.
        - rewrite sg_empty. 
            rewrite sp_empty.
            assumption.
        - simpl in *.
            destruct a as [X u].
            destruct (X =? x) eqn:eq; auto.
            injintrosubst HG. reflexivity.
    Qed.
End TypeSubstitution.
Module TS := TypeSubstitution.

Module Closed.
    (* Bound type variables. *)
    Definition bound : Type := list id.

    (* No free type variables in a type. *)
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

    (* No free type variables in a poly-type. *)
    Inductive cp (b : bound) : poly -> Prop :=
        | closed_type :
            forall (t : type),
            ct b t ->
            cp b (PType t)
        | closed_forall :
            forall (X : id) (p : poly),
            cp (X :: b) p ->
            cp b (PForall X p).

    Definition closed (p : poly) := cp [] p.

    (* Closed gamma. *)
    Definition cg (g : gamma) : Prop :=
        Forall (fun xp : id * poly =>
            let (_,p) := xp in closed p) g.
End Closed.
Module C := Closed.

Module FreeVariables.
    Fixpoint fvt (t : type) : IS.t :=
        match t with
        | TUnit => IS.empty
        | TVar X => IS.singleton X
        | TFun t1 t2 => IS.union (fvt t1) (fvt t2)
        end.

    Fixpoint fvp (p : poly) : IS.t :=
        match p with 
        | PType t => fvt t
        | PForall X p => IS.remove X (fvp p)
        end.

    Definition fvg : gamma -> IS.t :=
        fold_right 
            (fun (xp : id * poly) (Xs : IS.t) =>
                let (_,p) := xp in
                IS.union (fvp p) Xs) IS.empty.
End FreeVariables.
Module FV := FreeVariables.

Module Obtainable.
    (* t' is obtainable from t iff
        there exisst S such that S t = t'. *)
    Definition RT (t t' : type) := 
        exists (S : TS.T), TS.st S t = t'.
    
    Lemma RT_refl :
        forall (t : type), RT t t.
    Proof.
        intros t. exists iempty.
        apply TS.st_empty.
    Qed.

    Lemma RT_trans :
        forall (a b c : type),
        RT a b -> RT b c -> RT a c.
    Proof.
        unfold RT. intros a b c [s1 R1] [s2 R2].
        assert (TS.st s2 (TS.st s1 a) = c).
        - rewrite R1. assumption.
        - exists (TS.compose s1 s2).
            rewrite TS.st_compose.
            assumption.
    Qed.

    Lemma RT_sub :
        forall (t t' : type),
        RT t t' ->
        forall (s : TS.T),
        RT (TS.st s t) (TS.st s t').
    Proof.
        induction t; destruct t';
        intros [s' HR] s;
        try apply RT_refl;
        unfold RT; try discriminate.
        - exists s'. simpl in *.
    Abort.     

    (* p' is obtainable from p iff
        there exists S such that S p = p' *)
    Definition RP (p p' : poly) := 
        exists (S : TS.T), TS.sp S p = p'.

    Lemma RP_refl :
        forall (p : poly), RP p p.
    Proof.
        intros p. exists iempty.
        apply TS.sp_empty.
    Qed.

    Lemma RP_trans :
        forall (a b c : poly),
        RP a b -> RP b c -> RP a c.
    Proof.
        unfold RP. intros a b c [S1 R1] [S2 R2].
        assert (TS.sp S2 (TS.sp S1 a) = c).
        - rewrite R1. assumption.
        - exists (TS.compose S1 S2).
            rewrite TS.sp_compose.
            assumption.
    Qed.
End Obtainable.
Module O := Obtainable.

Module Instantiate.
    Inductive inst (s : TS.T) : poly -> type -> Prop :=
        | inst_type :
            forall (t : type),
            inst s (PType t) t
        | inst_forall :
            forall (X : id) (p : poly) (t' t : type),
            iget X s = Some t' ->
            inst s (TS.sp s p) t ->
            inst s (PForall X p) t.

    Definition instance (p : poly) (t : type) := 
        exists s : TS.T, inst s p t.

    Lemma instance_sub :
        forall (p : poly) (t : type),
        instance p t ->
        forall (S : TS.T),
        instance (TS.sp S p) (TS.st S t).
    Proof.
        unfold instance. 
        intros p t [s H] S.
        induction H.
        - exists iempty. constructor.
        - destruct IHinst as [s' H'].
            exists s. simpl.
            apply inst_forall with (t' := t'); auto.
    Abort.
End Instantiate.
Module I := Instantiate.

Module Inference.
    Inductive infer (g : gamma) : expr -> poly -> Prop :=
        | infer_unit : infer g EUnit (PType TUnit)
        | infer_var :
            forall (x : id) (p : poly),
            iget x g = Some p ->
            infer g (EVar x) p
        | infer_app :
            forall (e1 e2 : expr) (t t' : type),
            infer g e1 (PType (TFun t t')) ->
            infer g e2 (PType t) ->
            infer g (EApp e1 e2) (PType t')
        | infer_fun :
            forall (x : id) (e : expr) (t' t : type),
            infer (ibind x (PType t') g) e (PType t) ->
            infer g (EFun x e) (PType (TFun t' t))
        | infer_let :
            forall (x : id) (e e' : expr) (p : poly) (t : type),
            infer g e p ->
            infer (ibind x p g) e' (PType t) ->
            infer g (ELet x e e') (PType t)
        | infer_inst :
            forall (e : expr) (p p' : poly) (t : type) (X : id),
            TS.sp [(X,t)] p = p' ->
            infer g e (PForall X p) ->
            infer g e p'
        | infer_gen :
            forall (e : expr) (X : id) (p : poly),
            ~ IS.In X (FV.fvg g) ->
            infer g e p ->
            infer g e (PForall X p).

    Example identity_fun :
        infer iempty (EFun "x" (EVar "x")) 
            (PForall "A" (PType (TFun (TVar "A") (TVar "A")))).
    Proof.
        apply infer_gen.
        - simpl. apply IS.empty_spec.
        - repeat constructor.
    Qed.

    Example self_app :
        infer 
            (ibind "z" 
                (PForall "A" 
                    (PType (TFun (TVar "A") (TVar "A")))) iempty)
            (EApp (EVar "z") (EVar "z"))
            (PType (TFun (TVar "A") (TVar "A"))).
    Proof.
        apply infer_app with 
            (t := TFun (TVar "A") (TVar "A")).
        - apply infer_inst with 
            (p := PType (TFun (TVar "A") (TVar "A")))
            (t := TFun (TVar "A") (TVar "A")) (X := "A").
            + reflexivity.
            + repeat constructor.
        - apply infer_inst with 
            (p := PType (TFun (TVar "A") (TVar "A")))
            (t := TVar "A") (X := "A").
            + reflexivity.
            + repeat constructor.
    Qed.

    Example let_identity_self_app :
        infer iempty
            (ELet "z" (EFun "x" (EVar "x")) 
                (EApp (EVar "z") (EVar "z")))
            (PType (TFun (TVar "A") (TVar "A"))).
    Proof.
        apply infer_let with 
            (p := PForall "A" (PType (TFun (TVar "A") (TVar "A")))).
        - apply identity_fun.
        - apply self_app.
    Qed.

    Proposition infer_sub :
        forall (g : gamma) (e : expr) (p : poly),
        infer g e p ->
        forall (S : TS.T), 
        infer (TS.sg S g) e (TS.sp S p).
    Proof.
        intros g e p HI.
        induction HI; intros S; simpl in *.
        - constructor.
        - constructor. 
            apply TS.sg_get. assumption.
        - apply infer_app with (t := TS.st S t); auto.
        - constructor. apply IHHI.
        - apply infer_let with (p := TS.sp S p); auto.
            apply IHHI2.
        - apply infer_inst with 
            (p := TS.sp (iremove X S) p)
            (t := t) (X := X); auto.
            induction S.
            + rewrite <- TS.sp_compose. simpl.
                rewrite TS.sp_empty.
                assumption.
            + simpl. destruct a as [Y u].
                destruct (Y =? X) eqn:eq.
                * rewrite IHS. apply eqb_eq in eq.
                    subst. admit.
                * admit.
        - constructor. 
            + admit.
            + admit.
    Abort.
End Inference.