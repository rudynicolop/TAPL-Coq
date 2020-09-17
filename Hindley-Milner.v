Require Import String.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.
Require Coq.MSets.MSetProperties.
Module MSP := Coq.MSets.MSetProperties.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Import Coq.Logic.Decidable.
Require Coq.Logic.Classical_Pred_Type.
Module CPT := Coq.Logic.Classical_Pred_Type.
Require Import Coq.Program.Equality.
Require Coq.Logic.Classical_Prop.
Module CP := Coq.Logic.Classical_Prop.
Require Coq.FSets.FMapWeakList.
Module FMW := Coq.FSets.FMapWeakList.
Require Coq.FSets.FMapFacts.
Module FMF := Coq.FSets.FMapFacts.

(* standard library lemma *)
Axiom Forall_app : 
    forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.

(* Hindley-Milner Type-System *)

Ltac inv H := inversion H; subst.

Ltac injintrosubst H := injection H; intros; subst.

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

Module TypeSyntax.
    Inductive type : Type :=
        | TUnit
        | TVar (X : id)
        | TFun (t1 t2 : type).

    Definition names : Type := IS.t.

    Fixpoint fv (t : type) : names :=
        match t with
        | TUnit => IS.empty
        | TVar X => IS.singleton X
        | TFun t1 t2 => IS.union (fv t1) (fv t2)
        end.

    (* type variable in a type *)
    Fixpoint TIn (X : id) (t : type) : Prop :=
        match t with
        | TUnit => False
        | TVar Y => X = Y
        | TFun t1 t2 => TIn X t1 \/ TIn X t2
        end.
End TypeSyntax.
Export TypeSyntax.

(* Signature for type substitution. *)
Module Type Sigma.
    (* Sigma: maps type variables 
        to monomorphic types. *)
    Parameter t : Type.
    
    Parameter empty : t.

    Parameter bind : id -> type -> t -> t.

    Parameter get : id -> t -> option type.

    Axiom get_empty :
        forall (X : id), get X empty = None.

    Axiom bind_correct :
        forall (X : id) (ty : type) (s : t),
        get X (bind X ty s) = Some ty.

    Axiom bind_complete :
        forall {X Y : id}, Y <> X ->
        forall (s : t) (ty : type),
        get X (bind Y ty s) = get X s.

    (* Sigma composition:
        compose s1 s2 X = s2(s1(X)) *)
    Parameter compose : t -> t -> t.

    Axiom compose_empty :
        forall (s : t),
        compose empty s = s.

    Fixpoint sub_type (s : t) (t : type) : type :=
        match t with
        | TUnit => TUnit
        | TVar X => 
            match get X s with
            | None => TVar X
            | Some t' => t'
            end
        | TFun t1 t2 => TFun (sub_type s t1) (sub_type s t2)
        end.

    Axiom compose_correct :
        forall (s1 s2 : t) (ty : type),
        sub_type (compose s1 s2) ty = (sub_type s2 (sub_type s1 ty)).

    Axiom sub_type_bind_notin :
        forall (X : id) (ty : type),
        ~ TIn X ty ->
        forall (T : type),
        sub_type (bind X T empty) ty = ty.
End Sigma.

Module SigmaSubstitution(S : Sigma).
    Lemma sub_type_empty :
        forall (t : type),
        S.sub_type S.empty t = t.
    Proof.
        intros t. induction t; 
        try reflexivity; simpl.
        - rewrite S.get_empty. reflexivity.
        - rewrite IHt1. rewrite IHt2. reflexivity.
    Qed.

    Lemma sub_type_bind :
        forall (X : id) (ty : type) (s : S.t),
        ~ TIn X ty ->
        S.sub_type (S.compose (S.bind X ty S.empty) s) (TVar X) =
            S.sub_type (S.compose (S.bind X ty S.empty) s) ty.
    Proof.
        intros X ty s HIn.
        rewrite S.compose_correct.
        rewrite S.compose_correct. simpl. 
        destruct (X =? X)%string eqn:eq; 
        simpl in *.
        - rewrite S.bind_correct. 
            rewrite S.sub_type_bind_notin; auto.
        - apply eqb_neq in eq. contradiction.
    Qed.

    Lemma sub_type_bind_inj :
        forall (s : S.t) (X : id) (ty T : type),
        S.sub_type s (S.sub_type (S.bind X ty S.empty) T) =
        S.sub_type (S.compose (S.bind X ty S.empty) s) T.
    Proof.
        intros s X ty T. rewrite S.compose_correct.
        reflexivity.
    Qed.

    Definition eq (s1 s2 : S.t) :=
        forall (X : id), S.get X s1 = S.get X s2.

    Lemma eq_get :
        forall (s1 s2 : S.t),
        s1 = s2 -> eq s1 s2.
    Proof.
        intros s1 s2 H. subst.
        unfold eq. intros X.
        reflexivity.
    Qed.

    (* should change other definitions later... *)
    Axiom eq_extensional :
        forall (s1 s2 : S.t),
        eq s1 s2 -> s1 = s2.
End SigmaSubstitution.

Module ConstraintEquations.
    Definition equation : Type := type * type.

    Definition constraint : Type := list equation.

    (* type variable in an equation *)
    Fixpoint EQIn (X : id) (eq : equation) : Prop :=
        let (t1,t2) := eq in TIn X t1 \/ TIn X t2.

    (* type variable in a constraint *)
    Definition CIn (X : id) (C : constraint) : Prop :=
        Exists (EQIn X) C.
End ConstraintEquations.
Export ConstraintEquations.

Module Unification(S : Sigma).
    Module SS := SigmaSubstitution S.

    Definition satisfy_equation (s : S.t) (eq : equation) : Prop :=
        let (t1,t2) := eq in S.sub_type s t1 = S.sub_type s t2.

    Definition satisfy_constraint (s : S.t) (C : constraint) : Prop :=
    Forall (satisfy_equation s) C.

    Definition sub_equation (s : S.t) (eq : equation) : equation :=
            let (t1,t2) := eq in (S.sub_type s t1, S.sub_type s t2).

    Definition sub_constraint (s : S.t) (C : constraint) : constraint :=
        map (sub_equation s) C.

    Inductive unify : constraint -> S.t -> Prop :=
        | unify_nil : unify [] S.empty
        | unify_eq : 
            forall (t : type) (C : constraint) (s : S.t),
            unify C s ->
            unify ((t,t) :: C) s
        | unify_left_var :
            forall (X : id) (t : type) (C : constraint) (s : S.t),
            ~ TIn X t ->
            unify (sub_constraint (S.bind X t S.empty) C) s ->
            unify ((TVar X, t) :: C) (S.compose (S.bind X t S.empty) s)
        | unify_right_var :
            forall (X : id) (t : type) (C : constraint) (s : S.t),
            ~ TIn X t ->
            unify (sub_constraint (S.bind X t S.empty) C) s ->
            unify ((t, TVar X) :: C) (S.compose (S.bind X t S.empty) s)
        | unify_fun : 
            forall (a1 a2 b1 b2 : type) (C : constraint) (s : S.t),
            unify ((a1,a2) :: (b1,b2) :: C) s ->
            unify ((TFun a1 b1, TFun a2 b2) :: C) s.
        
    Definition more_general (s s' : S.t) : Prop :=
        exists (s'' : S.t), s' = S.compose s s''.

    Definition principal_unifier (C : constraint) (s : S.t) : Prop := 
        satisfy_constraint s C /\ 
        forall (s' : S.t), 
        satisfy_constraint s' C ->  more_general s s'.

    Lemma satisfy_equation_sym :
        forall (s : S.t) (t1 t2 : type),
        satisfy_equation s (t1,t2) ->
        satisfy_equation s (t2,t1).
    Proof.
        intros s t1 t2 H. 
        unfold satisfy_equation in *. auto.
    Qed.

    Lemma satisfy_constraint_compose :
        forall (s : S.t) (X : id) (t : type) (C : constraint),
        satisfy_constraint s (sub_constraint (S.bind X t S.empty) C) ->
        satisfy_constraint (S.compose (S.bind X t S.empty) s) C.
    Proof.
        intros s X t C H.
        unfold satisfy_constraint in *.
        induction C; constructor; inv H; auto.
        destruct a as [t1 t2].
        unfold satisfy_equation in *.
        simpl in H2. clear H3 IHC H.
        rewrite <- SS.sub_type_bind_inj.
        rewrite <- SS.sub_type_bind_inj.
        assumption.
    Qed.

    Lemma satisfy_equation_compose :
        forall (X : id) (t : type) (s : S.t),
        ~ TIn X t ->
        satisfy_equation (S.compose (S.bind X t S.empty) s) (TVar X, t).
    Proof.
        intros X t s HIn. unfold satisfy_equation.
        apply SS.sub_type_bind; auto.
    Qed.

    Theorem unify_correct : 
        forall (C : constraint) (s : S.t),
        unify C s -> satisfy_constraint s C.
    Proof.
        intros C s HU. induction HU; constructor; auto.
        - unfold satisfy_equation. reflexivity.
        - apply satisfy_equation_compose. assumption.
        - apply satisfy_constraint_compose. assumption.
        - apply satisfy_equation_sym.
            apply satisfy_equation_compose.
            assumption.
        - apply satisfy_constraint_compose. assumption.
        - inv IHHU. simpl in *. rewrite H1. inv H2.
            inv H3. rewrite H0. reflexivity.
        - inv IHHU. inv H2. assumption.
    Qed.

    Lemma satisfy_sub_type_equation :
        forall (X : id) (T : type) (s : S.t),
        (* ~ TIn X T -> *)
        satisfy_equation s (TVar X, T) ->
        forall (E : equation),
        satisfy_equation s E ->
        satisfy_equation s (sub_equation (S.bind X T S.empty) E).
    Proof.
        intros Z T s HS.
        intros [t1 t2]. generalize dependent t2.
        induction t1; induction t2; intros H; auto;
        try discriminate; simpl in *;
        try (destruct (IdDec.eq_dec X Z) as [HX | HX]; subst;
            try rewrite S.bind_correct;
            try (rewrite S.bind_complete; auto;
                rewrite S.get_empty; simpl);
                try rewrite HS in H;
                try rewrite H in HS;
                assumption);
        try (destruct (IdDec.eq_dec X0 Z) as [HX0 | HX0]; 
            destruct (IdDec.eq_dec X Z) as [HX | HX]; 
            subst; auto;
            try rewrite S.bind_correct;
            try rewrite S.bind_complete;
            try rewrite S.bind_complete; auto;
            try rewrite S.get_empty;
            try rewrite S.get_empty; auto; simpl;
            rewrite <- HS; assumption).
        - destruct (IdDec.eq_dec X Z) as [HXZ | HXZ]; subst.
            + rewrite S.bind_correct.
                rewrite HS in H.
                rewrite H.
                (* Induction is inaccurate...
                    perhaps need to define induction
                    for equations...?*)
                rewrite S.bind_correct in IHt2_2.
                rewrite S.bind_correct in IHt2_1.
                admit.
            + admit.
        - destruct (S.get X s) eqn:eq;
            try discriminate.
            destruct (IdDec.eq_dec X Z) as [HXZ | HXZ]; subst.
            + rewrite S.bind_correct.
                rewrite eq in HS. rewrite <- HS.
                admit.
            + admit.
        - injintrosubst H.
            apply IHt1_1 in H1.
            apply IHt1_2 in H0.
            rewrite H0. rewrite H1.
            reflexivity.
    Admitted.

    Lemma satisfy_sub_type_constraint :
        forall (X : id) (T : type) (s : S.t),
        (* ~ TIn X T -> *)
        satisfy_equation s (TVar X, T) ->
        forall (C : constraint),
        satisfy_constraint s C ->
        satisfy_constraint s (sub_constraint (S.bind X T S.empty) C).
    Proof.
        intros X T s HS C HC.
        unfold satisfy_constraint in *.
        induction HC; constructor; auto.
        apply satisfy_sub_type_equation; auto.
    Qed.

    Theorem unify_principal :
        forall (C : constraint) (s : S.t),
        unify C s -> principal_unifier C s.
    Proof.
        intros C s HU. unfold principal_unifier. split.
        - apply unify_correct; auto.
        - induction HU; try (intros s' HSC; unfold more_general).
            + exists s'. rewrite S.compose_empty.
                reflexivity.
            + inv HSC. apply IHHU in H2. assumption.
            + inv HSC.
                apply satisfy_sub_type_constraint 
                    with (C := C) in H2; auto.
                apply IHHU in H2.
                unfold more_general in H2.
                destruct H2 as [s'' HG].
                assert (Hs' : s' = S.compose (S.compose (S.bind X t S.empty) s) s'').
                { apply SS.eq_extensional.
                    apply SS.eq_get in HG.
                    unfold SS.eq in *.
                    intros Y. pose proof HG Y as HGY.
                    destruct (IdDec.eq_dec Y X); subst;
                    (* Need better notions of equality,
                        espeically with respect to composition. *)
                    admit. }
                { exists s''. assumption. }
            + admit.
            + assert (H : satisfy_constraint 
                s' ((a1, a2) :: (b1, b2) :: C)).
                * inv HSC. inv H1.
                    constructor; auto.
                * apply IHHU in H. assumption.
    Admitted.
End Unification.

Module Monomorphic.
    Section TypeMap.
        Context {T : Type}.

        Definition tmap := id -> option T.

        Definition tempty : tmap := fun x => None.

        Definition bind (x : id) (t : T) (m : tmap) : tmap :=
            fun y => if (x =? y)%string then Some t else m y.

        Lemma bind_correct : 
            forall (x : id) (t : T) (m : tmap),
            bind x t m x = Some t.
        Proof.
            intros. unfold bind. destruct ((x =? x)%string) eqn:eq.
            - reflexivity.
            - apply eqb_neq in eq. contradiction.
        Qed.

        Lemma bind_complete :
            forall (x x' : id) (t t' : T),
            x' <> x -> 
            forall (m : tmap),
            (m x = Some t <-> bind x' t' m x = Some t). 
        Proof.
            intros. unfold bind. apply eqb_neq in H. 
            rewrite H. split; intros; apply H0.
        Qed.

        Lemma rebind_correct : 
            forall (x : id) (t t' : T) (m : tmap),
            bind x t m = bind x t (bind x t' m).
        Proof.
            intros. apply functional_extensionality. intros y.
            unfold bind. destruct ((x =? y)%string); reflexivity.
        Qed.

        Lemma bind_diff_comm : 
            forall (x y : id) (u v : T) (m : tmap),
            x <> y ->
            bind x u (bind y v m) = bind y v (bind x u m).
        Proof.
            intros. apply functional_extensionality. intros z.
            unfold bind. destruct ((x =? z)%string) eqn:eq.
                - apply eqb_eq in eq; subst.
                    destruct ((y =? z)%string) eqn:eeq.
                    + apply eqb_eq in eeq; subst. contradiction.
                    + reflexivity.
                - apply eqb_neq in eq. destruct ((y =? z)%string) eqn:eeq; reflexivity.
        Qed.
    End TypeMap.
    Definition bind_correct_type := @bind_correct type.

    Module Syntax.
        Inductive expr : Type :=
            | EUnit
            | EVar (x : id)
            | EFun (x : id) (t : type) (e : expr)
            | EApp (e1 e2 : expr).

        (* type variable in an expression *)
        Fixpoint EIn (X : id) (e : expr) : Prop :=
            match e with
            | EUnit | EVar _ => False
            | EFun _ t e => TIn X t \/ EIn X e
            | EApp e1 e2 => EIn X e1 \/ EIn X e2
            end.
    End Syntax.
    Export Syntax.

    Section TypeCheck.
        Definition gamma : Type := @tmap type.

        Inductive check (g : gamma) : expr -> type -> Prop :=
            | check_unit : 
                check g EUnit TUnit
            | check_var : 
                forall (x : id) (t : type), 
                g x = Some t ->
                check g (EVar x) t
            | check_fun : 
                forall (x : id) (t1 t2 : type) (e : expr),
                check (bind x t1 g) e t2 ->
                check g (EFun x t1 e) (TFun t1 t2)
            | check_app :
                forall (e1 e2 : expr) (t1 t2 : type),
                check g e1 (TFun t1 t2) ->
                check g e2 t1 ->
                check g (EApp e1 e2) t2.
    End TypeCheck.

    Module S <: Sigma.
        Definition t : Type := @tmap type.

        Definition empty : t := tempty.
        
        Definition bind : id -> type -> t -> t := bind.
    
        Definition get (x :id) (s : S.t) : option type := s x.

        Lemma bind_get_eta_eq :
            forall (X Y : id) (s : t) (ty : type),
            bind X ty s Y = get Y (bind X ty s).
        Proof. intros X Y s ty. reflexivity. Qed.

        Lemma get_empty :
            forall (X : id), get X empty = None.
        Proof. intros X. reflexivity. Qed.

        Lemma bind_correct :
            forall (x : id) (ty : type) (s : t),
            get x (bind x ty s) = Some ty.
        Proof. intros x ty s. apply bind_correct. Qed.

        Lemma bind_complete :
            forall {x y : id}, y <> x ->
            forall (s : t) (ty : type),
            get x (bind y ty s) = get x s.
        Proof.
            intros x y Hxy s ty. unfold get.
            unfold bind. unfold Monomorphic.bind.
            apply eqb_neq in Hxy. rewrite Hxy.
            reflexivity.
        Qed.

        Fixpoint sub_type (s : t) (t : type) : type :=
            match t with
            | TUnit => TUnit
            | TVar X => 
                match get X s with
                | None => TVar X
                | Some t' => t'
                end
            | TFun t1 t2 => TFun (sub_type s t1) (sub_type s t2)
            end.

        Definition compose (s1 s2 : t) : t :=
            fun X => 
                match get X s1 with
                | None => get X s2
                | Some t => Some (sub_type s2 t)
                end.

        Lemma compose_empty :
            forall (s : t),
            s = compose empty s.
        Proof.
            intros s. apply functional_extensionality.
            intros x. reflexivity.
        Qed.

        Lemma compose_correct :
            forall (s1 s2 : t) (ty : type),
            sub_type (compose s1 s2) ty = (sub_type s2 (sub_type s1 ty)).
        Proof.
            intros s1 s2 ty. induction ty; 
            auto; simpl.
            - unfold compose; unfold get.
                destruct (s1 X) eqn:eq; auto.
            - rewrite IHty1. rewrite IHty2.
                reflexivity.
        Qed.

        Lemma sub_type_bind_notin :
            forall (X : id) (ty : type),
            ~ TIn X ty ->
            forall (T : type),
            sub_type (bind X T empty) ty = ty.
        Proof.
            intros X ty. induction ty; 
            intros HIn T; simpl in *; auto.
            - rewrite bind_complete; auto.
            - apply CP.not_or_and in HIn as [H1 H2].
                apply IHty1 with (T := T) in H1.
                apply IHty2 with (T := T) in H2.
                rewrite H1. rewrite H2. reflexivity.
        Qed.
    End S.

    Module SS := SigmaSubstitution S.

    Section TypeSubstitution.
        Definition sub_gamma (s : S.t) (g : gamma) : gamma :=
            fun x =>
                match g x with
                | None => None
                | Some t => Some (S.sub_type s t)
                end.

        Fixpoint sub_expr (s : S.t) (e : expr) : expr :=
            match e with
            | EUnit => EUnit
            | EVar x => EVar x
            | EFun x t e => EFun x (S.sub_type s t) (sub_expr s e)
            | EApp e1 e2 => EApp (sub_expr s e1) (sub_expr s e2)
            end.
        
        Lemma bind_sub_gamma :
            forall (s : S.t) (g : gamma) (x : id) (t : type),
            sub_gamma s (bind x t g) = bind x (S.sub_type s t) (sub_gamma s g).
        Proof.
            intros s g x t. 
            apply functional_extensionality.
            intros y. 
            destruct (IdDec.eq_dec x y); 
            subst; simpl;
            unfold sub_gamma;
            try rewrite bind_correct;
            try rewrite bind_correct;
            try reflexivity.
            unfold bind.
            apply eqb_neq in n as HF.
            rewrite HF. reflexivity.
        Qed.

        Theorem substutution_preserves_typing :
            forall (g : gamma) (e : expr) (t : type),
            check g e t ->
            forall (s : S.t),
            check (sub_gamma s g) (sub_expr s e) (S.sub_type s t).
        Proof.
            intros g e t H. induction H; intros s; try constructor.
            - unfold sub_gamma. rewrite H. reflexivity.
            - fold S.sub_type. fold sub_expr.
                rewrite <- bind_sub_gamma.
                apply IHcheck.
            - apply check_app with (t1 := S.sub_type s t1);
                fold sub_expr; auto.
                specialize IHcheck1 with (s := s).
                simpl in IHcheck1. assumption.
        Qed.

        Definition solution (g : gamma) (e : expr) (s : S.t) (t : type) : Prop :=
        check (sub_gamma s g) (sub_expr s e) t.
    End TypeSubstitution.

    Module U := Unification S.
    Export U.

    Module ConstraintTyping.
        (* type variable not in gamma *)
        Definition GNIn (X : id) (g : gamma) : Prop :=
            forall (x : id) (t : type),
            g x = Some t -> ~ TIn X t.

        Inductive constraint_type (g : gamma) 
        : expr -> type -> names -> constraint -> Prop :=
            | ct_unit : 
                constraint_type g EUnit TUnit IS.empty []
            | ct_var :
                forall (x : id) (t : type),
                g x = Some t ->
                constraint_type g (EVar x) t IS.empty []
            | ct_fun :
                forall (x : id) (t1 t2 : type) 
                    (e : expr) (X : names) (C : constraint),
                constraint_type (bind x t1 g) e t2 X C ->
                constraint_type g (EFun x t1 e) (TFun t1 t2) X C
            | ct_app :
                forall (e1 e2 : expr) (t1 t2 : type) (X : id)
                    (X1 X2 : names) (C1 C2 : constraint),
                constraint_type g e1 t1 X1 C1 ->
                constraint_type g e2 t2 X2 C2 ->
                IS.Empty (IS.inter X1 X2) ->
                IS.Empty (IS.inter X1 (fv t2)) ->
                IS.Empty (IS.inter X2 (fv t1)) ->
                ~ IS.In X X1 -> ~ IS.In X X2 ->
                ~ TIn X t1 -> ~ TIn X t2 ->
                ~ EIn X e1 -> ~ EIn X e2 ->
                ~ CIn X C1 -> ~ CIn X C2 -> GNIn X g ->
                constraint_type g (EApp e1 e2) (TVar X)
                    (IS.add X (IS.union X1 X2))
                    ((t1, TFun t2 (TVar X)) :: C1 ++ C2).

        Definition constraint_solution
        {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
        (H : constraint_type g e t X C) (s : S.t) (T : type) : Prop :=
        satisfy_constraint s C /\ S.sub_type s t = T.

        Theorem Constraint_Typing_Sound : 
            forall (g : gamma) (e : expr) (t : type) 
                (X : names) (C : constraint) 
                (H : constraint_type g e t X C) 
                (s : S.t) (T : type),
            constraint_solution H s T -> solution g e s T.
        Proof.
            intros g e t X C H s T HCS.
            destruct HCS as [HSC HSE].
            unfold solution. subst.
            induction H.
            - constructor.
            - apply substutution_preserves_typing.
                constructor; auto.
            - constructor.
                fold S.sub_type. fold sub_expr.
                rewrite <- bind_sub_gamma. auto.
            - inv HSC.
                apply Forall_app in H16 as [HC1 HC2].
                apply check_app with (t1 := S.sub_type s t2); auto.
                fold sub_expr.
                apply IHconstraint_type1 in HC1.
                unfold satisfy_equation in H15.
                rewrite H15 in HC1. simpl in HC1.
                assumption.
        Qed.

        (* s/N *)
        Definition sigma_diff (s : S.t) (N : names) : S.t := 
            fun X => if IS.mem X N then None else s X.

        Theorem Constraint_Typing_Complete : 
            forall (g : gamma) (e : expr) (t : type) 
            (X : names) (C : constraint) 
            (H : constraint_type g e t X C) 
            (s : S.t) (T : type),
            sigma_diff s X = s ->
            solution g e s T ->
            exists (s' : S.t),
            sigma_diff s' X = s /\ constraint_solution H s' T.
        Proof.
            intros g e t X C H.
            (* Coq won't let me do induction on H *)
            (* induction H. *)
        Abort.
    End ConstraintTyping.
    Export ConstraintTyping.

    Section PrincipalTypes.
        Definition principal_solution
        {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
        (H : constraint_type g e t X C) (s : S.t) (T : type) : Prop :=
        constraint_solution H s T /\
        forall (s' : S.t) (T' : type),
        constraint_solution H s' T' -> more_general s s'.

        Corollary unify_principal_solution :
            forall {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
                (H : constraint_type g e t X C) (s : S.t),
            unify C s ->
            principal_solution H s (S.sub_type s t).
        Proof.
            intros g e t X C H s HU.
            apply unify_principal in HU as HUC.
            unfold principal_unifier in HUC.
            unfold principal_solution.
            destruct HUC as [HSC HMG]. split.
            - unfold constraint_solution. split; auto.
            - intros s' T' Hs'T'.
                unfold constraint_solution in Hs'T'.
                destruct Hs'T' as [HSCs' HSTs']. auto.
        Qed.

        Lemma constraint_solution_unify :
            forall {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
                (H : constraint_type g e t X C) (s' : S.t) (T' : type),
            constraint_solution H s' T' ->
            exists (s : S.t), unify C s.
        Proof.
            intros g e t X C H s' T' HCS.
            unfold constraint_solution in HCS.
            destruct HCS as [HSC HST].
            dependent induction H; simpl in *;
            try (exists tempty; apply unify_nil).
            - apply IHconstraint_type
                with (T' := S.sub_type s' t2) in HSC; auto.
            - inv HSC. apply Forall_app in H16 as [HC1 HC2].
                apply IHconstraint_type1 
                    with (T' := S.sub_type s' t1) in HC1; auto.
                apply IHconstraint_type2
                    with (T' := S.sub_type s' t2) in HC2; auto.
                destruct HC1 as [s1 HU1].
                destruct HC2 as [s2 HU2].
                destruct t1.
                + inv H15.
                + exists (S.compose (S.bind X0 (TFun t2 (TVar X)) tempty) (S.compose s1 s2)).
                    constructor; admit.
                + exists (S.compose s1 s2).
                    constructor. admit.
        Admitted.

        Theorem principal_types :
            forall {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
                (H : constraint_type g e t X C),
            (exists (s' : S.t) (T' : type), constraint_solution H s' T') ->
            exists (s : S.t) (T : type), principal_solution H s T.
        Proof.
            intros g e t X C H [s' [T' HCS]].
            apply constraint_solution_unify in HCS.
            destruct HCS as [s HU].
            exists s. exists (S.sub_type s t).
            apply unify_principal_solution; auto.
        Qed.

        (* Interleave constraint generation and unification. 
            Should generate a principal type at each step. *)
        Inductive interleave (g : gamma) : expr -> type -> Prop :=
            | il_unit : interleave g EUnit TUnit
            | il_var : 
                forall (x : id) (t : type),
                g x = Some t ->
                interleave g (EVar x) t
            | il_fun :
                forall (x : id) (t1 t2 : type) (e : expr),
                interleave (bind x t1 g) e t2 ->
                interleave g (EFun x t1 e) (TFun t1 t2)
            | il_app :
                forall (e1 e2 : expr) (t1 t2 : type) (X : id) (s : S.t),
                interleave g e1 t1 ->
                interleave g e2 t2 ->
                ~ TIn X t1 -> ~ TIn X t2 ->
                ~ EIn X e1 -> ~ EIn X e2 -> GNIn X g ->
                unify [(t1, TFun t2 (TVar X))] s ->
                interleave g (EApp e1 e2) (S.sub_type s (TVar X)).

        Proposition interleave_sound :
            forall (g : gamma) (e : expr) (t : type),
            interleave g e t ->
            forall (N : names) (C : constraint)
                (H : constraint_type g e t N C),
            exists (s : S.t), unify C s /\ constraint_solution H s t.
        Proof.
            intros g e t HIL. 
            induction HIL; intros N C HCT; inv HCT;
            unfold constraint_solution.
            - exists tempty. repeat split; constructor.
            - exists tempty. repeat split; 
                try constructor. apply SS.sub_type_empty.
            - pose proof IHHIL N C H5 as IH.
                destruct IH as [s [HU HCS]].
                unfold constraint_solution in HCS.
                exists s. destruct HCS as [HSC HST].
                repeat split; auto.
                simpl. rewrite HST. admit.
            - admit.
            (* white flag. *)
            (* pose proof IHHIL1 X1 C1 H8 as IH1. *)
        Abort.
    End PrincipalTypes.

    Section Examples.
        Ltac ex222 t :=
            apply check_app with (t1 := t);
            constructor; reflexivity.

        Definition f : id := "f".
        Definition a : id := "a".
        Definition x : id := "x".
        Definition y : id := "y".
        Definition z : id := "z".
        Definition X : id := "X".
        Definition Y : id := "Y".
        Definition Z : id := "Z".
        
        Definition g : gamma := bind f (TVar X) (bind a (TVar Y) tempty).
        Definition e : expr := EApp (EVar f) (EVar a).
        
        Example ex2221 : 
            solution g e (S.bind X (TFun (TVar Y) TUnit) tempty) TUnit.
        Proof. ex222 (TVar Y). Qed.

        Example ex2222 :
            solution g e (S.bind X (TFun (TVar Y) (TVar Z)) (S.bind Z TUnit tempty)) (TVar Z).
        Proof. ex222 (TVar Y). Qed.

        Example ex2223 :
            solution g e (S.bind X (TFun TUnit TUnit) (S.bind Y TUnit tempty)) TUnit.
        Proof. ex222 TUnit. Qed.

        Example ex224 :
            solution g e (S.bind X (TFun (TVar Y) (TVar Z)) tempty) (TVar Z).
        Proof. ex222 (TVar Y). Qed.
        
        Example ex2225 :
            solution g e (S.bind X (TFun (TVar Y) (TFun TUnit TUnit)) tempty) (TFun TUnit TUnit).
        Proof. ex222 (TVar Y). Qed.

        Definition term : expr := 
            EFun x (TVar X) (EFun y (TVar Y) (EFun z (TVar Z) 
                (EApp (EApp (EVar x) (EVar z)) (EApp (EVar y) (EVar z))))).

        Example ex2231 : 
            let s := (bind Y (TFun (TVar Z) TUnit) (bind X (TFun (TVar Z) (TFun TUnit TUnit)) tempty)) in
            solution tempty term s (S.sub_type s (TFun (TVar X) (TFun (TVar Y) (TFun (TVar Z) TUnit)))).
        Proof.
            unfold solution. simpl.
            repeat apply check_fun.
            apply check_app with (t1 := TUnit).
            - apply check_app with (t1 := TVar Z);
                constructor; reflexivity.
            - apply check_app with (t1 := TVar Z);
                constructor; reflexivity.
        Qed.

        Ltac ct_app_apply :=
            apply ct_app; 
            try (intros HF; simpl in HF;
                subst; discriminate);
            try (intros HF; simpl in HF;
                subst; contradiction).

        (* MSet library is a pain to work with... *)
        Axiom empty_inter :
            forall (x y : id),
            x <> y <-> 
            IS.Empty (IS.inter (IS.singleton x) (IS.singleton y)).

        Example ex2233 :
            exists (t : type) (N : names) (C : constraint),
            constraint_type tempty term t N C.
        Proof.
            unfold term.
            remember "T" as T in *.
            remember "U" as U in *.
            remember "V" as V in *.
            remember "W" as W in *.
            exists (TFun (TVar X) (TFun (TVar Y) (TFun (TVar Z) (TVar W)))).
            exists (IS.add W 
                (IS.union 
                    (IS.add U (IS.union IS.empty IS.empty))
                    (IS.add V (IS.union IS.empty IS.empty)))).
            exists ((TVar U, TFun (TVar V) (TVar W)) :: 
                ((TVar X, TFun (TVar Z) (TVar U)) :: [] ++ []) ++
                ((TVar Y, TFun (TVar Z) (TVar V)) :: [] ++ [])).
            repeat apply ct_fun.
            ct_app_apply.
            - ct_app_apply;
                try (constructor; reflexivity);
                try apply ISP.empty_inter_1;
                try apply ISP.empty_inter_2;
                try apply IS.empty_spec.
                + intros HF; inv HF.
                + intros HF; inv HF.
                + intros q Q Hq HIn.
                    destruct (IdDec.eq_dec z q) as [Hqz | Hqz];
                    destruct (IdDec.eq_dec y q) as [Hqy | Hqy];
                    destruct (IdDec.eq_dec x q) as [Hqx | Hqx];
                    try rewrite Hqz in *; 
                    try rewrite Hqy in *;
                    try rewrite Hqx in *;
                    try (rewrite <- (bind_complete q z Q (TVar Z) Hqz) in Hq);
                    try (rewrite <- (bind_complete q y Q (TVar Y) Hqy) in Hq);
                    try (rewrite bind_correct in Hq;
                        injintrosubst Hq; simpl in HIn;
                        discriminate).
                    unfold bind in Hq.
                    apply eqb_neq in Hqx. rewrite Hqx in Hq.
                    unfold tempty in Hq. discriminate.
            - ct_app_apply;
                try (constructor; reflexivity);
                try apply ISP.empty_inter_1;
                try apply ISP.empty_inter_2;
                try apply IS.empty_spec.
                + intros HF; inv HF.
                + intros HF; inv HF.
                + intros q Q Hq HIn.
                    destruct (IdDec.eq_dec z q) as [Hqz | Hqz];
                    destruct (IdDec.eq_dec y q) as [Hqy | Hqy];
                    destruct (IdDec.eq_dec x q) as [Hqx | Hqx];
                    try rewrite Hqz in *; 
                    try rewrite Hqy in *;
                    try rewrite Hqx in *;
                    try (rewrite <- (bind_complete q z Q (TVar Z) Hqz) in Hq);
                    try (rewrite <- (bind_complete q y Q (TVar Y) Hqy) in Hq);
                    try (rewrite bind_correct in Hq;
                        injintrosubst Hq; simpl in HIn;
                        discriminate).
                    unfold bind in Hq.
                    apply eqb_neq in Hqx. rewrite Hqx in Hq.
                    unfold tempty in Hq. discriminate.
            - rewrite ISP.empty_union_1; auto.
                rewrite <- ISP.singleton_equal_add.
                rewrite <- ISP.singleton_equal_add.
                apply empty_inter. intros HVU.
                subst. discriminate.
            - rewrite ISP.empty_union_1; auto.
                rewrite <- ISP.singleton_equal_add. simpl.
                apply empty_inter. intros HVU.
                subst. discriminate.
            - rewrite ISP.empty_union_1; auto.
                rewrite <- ISP.singleton_equal_add. simpl.
                apply empty_inter. intros HVU.
                subst. discriminate.
            - intros HF.
                rewrite ISP.empty_union_1 in HF; auto.
                rewrite <- ISP.singleton_equal_add in HF.
                inv HF; try discriminate. inv H0.
            - intros HF.
                rewrite ISP.empty_union_1 in HF; auto.
                rewrite <- ISP.singleton_equal_add in HF.
                inv HF; try discriminate. inv H0.
            - intros HF. simpl in HF. 
                destruct HF as [HF | HF]; contradiction.
            - intros HF. simpl in HF. 
                destruct HF as [HF | HF]; contradiction.
            - intros HF. simpl in HF. inv HF.
                + destruct H0 as [HX | [HZ | HU]];
                    discriminate.
                + inv H0.
            - intros HF. simpl in HF. inv HF.
                + destruct H0 as [HX | [HZ | HU]];
                    discriminate.
                + inv H0.
            - intros q Q Hq HIn.
                destruct (IdDec.eq_dec z q) as [Hqz | Hqz];
                destruct (IdDec.eq_dec y q) as [Hqy | Hqy];
                destruct (IdDec.eq_dec x q) as [Hqx | Hqx];
                try rewrite Hqz in *; 
                try rewrite Hqy in *;
                try rewrite Hqx in *;
                try (rewrite <- (bind_complete q z Q (TVar Z) Hqz) in Hq);
                try (rewrite <- (bind_complete q y Q (TVar Y) Hqy) in Hq);
                try (rewrite bind_correct in Hq;
                    injintrosubst Hq; simpl in HIn;
                    discriminate).
                unfold bind in Hq.
                apply eqb_neq in Hqx. rewrite Hqx in Hq.
                unfold tempty in Hq. discriminate.
        Qed.
    End Examples.
End Monomorphic.

Module Polymorphic.
    Section Syntax.
        Inductive poly : Type :=
            | PType (t : type)
            | PForall (X : id) (t : poly).

        (* isomorphic to poly. *)
        Definition scheme : Type := list id * type.
        
        (* Isomorphism. *)

        Fixpoint to_scheme (p : poly) : scheme :=
            match p with
            | PType t => ([],t)
            | PForall X p =>
                let (N,t) := to_scheme p in
                (X::N,t)
            end.

        Fixpoint to_poly' (N : list id) (t : type) : poly :=
            match N with
            | [] => PType t
            | X::N => PForall X (to_poly' N t)
            end.

        Definition to_poly (sch : scheme) : poly :=
            let (N,t) := sch in to_poly' N t.

        Lemma scheme_to_scheme :
            forall (sch : scheme),
            to_scheme (to_poly sch) = sch.
        Proof.
            intros [N t]. induction N; try reflexivity.
            simpl in *. rewrite IHN. reflexivity.
        Qed.

        Lemma poly_to_poly :
            forall (p : poly),
            to_poly (to_scheme p) = p.
        Proof.
            intros p. induction p; try reflexivity.
            simpl in *. destruct (to_scheme p).
            simpl. unfold to_poly in IHp.
            rewrite IHp. reflexivity.
        Qed.

        Inductive expr : Type :=
            | EUnit
            | EVar (x : id)
            | EFun (x : id) (t : type) (e : expr)
            | EApp (e1 e2 : expr)
            | ELet (x : id) (e1 e2 : expr).
    End Syntax.

    Section TypeMap.
        Context {T : Type}.

        Definition tmap : Type := list (id * T).

        Definition tempty : tmap := [].

        Definition tbind (x : id) (t : T) (m : tmap) : tmap := (x, t) :: m.

        Fixpoint tremove (x : id) (m : tmap) : tmap :=
            match m with
            | [] => []
            | (y,t) :: m =>
                if (y =? x)%string then (tremove x m) else (y,t) :: (tremove x m)
            end.

        Fixpoint tget (X : id) (m : tmap) : option T :=
            match m with
            | [] => None
            | (Y,t)::m => if (Y =? X)%string then Some t else tget X m
            end.
    End TypeMap.
    
    (* typing context *)
    Definition gamma : Type := @tmap poly.

    Module S <: Sigma.
        Definition t : Type := @tmap type.
        
        Definition empty : t := tempty.

        Definition bind : id -> type -> t -> t := tbind.
        
        Definition get : id -> t -> option type := tget.

        Lemma get_empty : 
            forall (X : id), get X empty = None.
        Proof. intros X. reflexivity. Qed.

        Lemma bind_correct :
            forall (X : id) (ty : type) (s : t),
            get X (bind X ty s) = Some ty.
        Proof.
            intros X ty s. cbn.
            destruct (X =? X) eqn:eq; auto.
            apply eqb_neq in eq. contradiction.
        Qed.

        Lemma bind_complete :
            forall {X Y : id}, Y <> X ->
            forall (s : t) (ty : type),
            get X (bind Y ty s) = get X s.
        Proof.
            intros X Y HYX s ty. cbn.
            apply eqb_neq in HYX. rewrite HYX.
            reflexivity.
        Qed.

        Fixpoint sub_type (s : t) (t : type) : type :=
            match t with
            | TUnit => TUnit
            | TVar X => 
                match get X s with
                | None => TVar X
                | Some t' => t'
                end
            | TFun t1 t2 => TFun (sub_type s t1) (sub_type s t2)
            end.

        Lemma sub_type_empty :
            forall (t : type),
            sub_type empty t = t.
        Proof.
            intros t. induction t; try reflexivity. simpl. 
            rewrite IHt1. rewrite IHt2. reflexivity.
        Qed.

        Fixpoint compose (s1 s2 : S.t) : S.t :=
            match s1 with
            | [] => s2
            | (X, T) :: s1 => (X, sub_type s2 T) :: compose s1 s2
            end.

        Lemma compose_empty :
            forall (s : t),
            compose empty s = s.
        Proof. intros s. reflexivity. Qed.

        Lemma compose_correct :
            forall (s1 s2 : t) (ty : type),
            sub_type (compose s1 s2) ty = (sub_type s2 (sub_type s1 ty)).
        Proof.
            intros s1 s2 ty. induction ty; 
            auto; simpl in *.
            - induction s1; simpl; auto.
                destruct a as [Y T]. simpl.
                destruct (Y =? X) eqn:eq; auto.
            - rewrite IHty1. rewrite IHty2.
                reflexivity.
        Qed.

        Lemma sub_type_bind_notin :
            forall (X : id) (ty : type),
            ~ TIn X ty ->
            forall (T : type),
            sub_type (bind X T empty) ty = ty.
        Proof.
            intros X ty Hin T. induction ty; 
            simpl in *; auto.
            - apply eqb_neq in Hin. rewrite Hin.
                reflexivity.
            - apply CP.not_or_and in Hin as [H1 H2].
                apply IHty1 in H1. apply IHty2 in H2.
                rewrite H1. rewrite H2. reflexivity.
        Qed.
    End S.
    
    Section TypeSubstitution.
        Fixpoint sub_expr (s : S.t) (e : expr) : expr :=
            match e with
            | EUnit => EUnit
            | EVar x => EVar x
            | EFun x t e => EFun x (S.sub_type s t) (sub_expr s e)
            | EApp e1 e2 => EApp (sub_expr s e1) (sub_expr s e2)
            | ELet x e1 e2 => ELet x (sub_expr s e1) (sub_expr s e2)
            end.

        Fixpoint sub_poly (s : S.t) (p : poly) : poly :=
            match p with
            | PType t => PType (S.sub_type s t)
            | PForall X p =>
                PForall X (sub_poly (tremove X s) p)
            end.

        Definition sub_gamma (s : S.t) : gamma -> gamma := 
            map (fun (e : id * poly) =>
                let (x,p) := e in (x, sub_poly s p)).
    End TypeSubstitution.

    Module SS := SigmaSubstitution S.

    Module U := Unification S.
    Export U.

    Section ConstraintTyping.
        (* type name in a poly-type, accounting for bound type names *)
        Fixpoint PIn (X : id) (p : poly) : Prop :=
            match p with
            | PType t => TIn X t
            | PForall Y p => X <> Y /\ PIn X p
            end.

        (* type variable in gamma *)
        Definition GIn (X : id) (g : gamma) : Prop :=
            exists (x : id) (p : poly), 
            tget x g = Some p /\ PIn X p.

        (* type variable not in gamma *)
        Definition GNIn (X : id) (g : gamma) : Prop :=
            forall (x : id) (p : poly), 
            tget x g = Some p -> ~ PIn X p.

        (* type variable in an expression *)
        Fixpoint EIn (X : id) (e : expr) : Prop :=
            match e with
            | EUnit | EVar _ => False
            | EFun _ t e => TIn X t \/ EIn X e
            | EApp e1 e2 | ELet _ e1 e2 => EIn X e1 \/ EIn X e2
            end.

        (* complete substitution of a poly-type to get 
            a type with fresh type variables *)
        Inductive sub_poly_type (g : gamma) (s : S.t) 
        : poly -> type -> names -> constraint -> Prop :=
            | spt_type : 
                forall (t t' : type), 
                S.sub_type s t = t' ->
                sub_poly_type g s (PType t) t' IS.empty []
            | spt_forall :
                forall (X Y : id) (p : poly) 
                    (N : names) (C : constraint) (t : type),
                GNIn Y g -> ~ PIn Y p -> ~ IS.In Y N ->
                sub_poly_type g (S.bind X (TVar Y) s) p t N C ->
                sub_poly_type g s (PForall X p) t (IS.add Y N) ((TVar X, TVar Y) :: C).

        Definition make_fun_poly (p1 p2 : poly) : poly :=
            let (N1,t1') := to_scheme p1 in
            let (N2,t2') := to_scheme p2 in
            to_poly (N1 ++ N2, TFun t1' t2').

        (* generalizes unbound type variables *)
        Inductive generalize_names (g : gamma) : type -> poly -> Prop :=
            | gun_unit : generalize_names g TUnit (PType TUnit)
            | gun_var_bound :
                forall (X : id),
                GIn X g ->
                generalize_names g (TVar X) (PType (TVar X))
            | gun_var_free :
                forall (X : id),
                ~ GIn X g ->
                generalize_names g (TVar X) (PForall X (PType (TVar X)))
            | gun_fun :
                forall (t1 t2 : type) (p1 p2 p : poly),
                p = make_fun_poly p1 p2 ->
                generalize_names g t1 p1 ->
                generalize_names g t2 p2 ->
                generalize_names g (TFun t1 t2) p.

        Inductive constraint_type (g : gamma) 
        : expr -> type -> names -> constraint -> Prop :=
            | ct_unit : 
                constraint_type g EUnit TUnit IS.empty []
            | ct_var :
                forall (x : id) (p : poly) (t : type) 
                    (N : names) (C : constraint),
                tget x g = Some p ->
                sub_poly_type g S.empty p t N C ->
                constraint_type g (EVar x) t N C
            | ct_fun :
                forall (x : id) (t1 t2 : type) 
                    (e : expr) (N : names) (C : constraint),
                constraint_type (tbind x (PType t1) g) e t2 N C ->
                constraint_type g (EFun x t1 e) (TFun t1 t2) N C
            | ct_app :
                forall (e1 e2 : expr) (t1 t2 : type) (X : id)
                    (N1 N2 : names) (C1 C2 : constraint),
                constraint_type g e1 t1 N1 C1 ->
                constraint_type g e2 t2 N2 C2 ->
                IS.Empty (IS.inter N1 N2) ->
                IS.Empty (IS.inter N1 (fv t2)) ->
                IS.Empty (IS.inter N2 (fv t1)) ->
                ~ IS.In X N1 -> ~ IS.In X N2 ->
                ~ TIn X t1 -> ~ TIn X t2 ->
                ~ EIn X e1 -> ~ EIn X e2 ->
                ~ CIn X C1 -> ~ CIn X C2 -> ~ GIn X g ->
                constraint_type g (EApp e1 e2) (TVar X)
                    (IS.add X (IS.union N1 N2))
                    ((t1, TFun t2 (TVar X)) :: C1 ++ C2)
            | ct_let :
                forall (x : id) (e1 e2 : expr) (t1 t2 : type)
                    (p1 : poly) (N1 N2 : names) (C1 C2 : constraint),
                    constraint_type g e1 t1 N1 C1 ->
                    generalize_names g t1 p1 ->
                    constraint_type (tbind x p1 g) e2 t2 N2 C2 ->
                    IS.Empty (IS.inter N1 N2) ->
                    IS.Empty (IS.inter N1 (fv t2)) ->
                    IS.Empty (IS.inter N2 (fv t1)) ->
                    constraint_type g (ELet x e1 e2) t2
                        (IS.union N1 N2) (C1 ++ C2).

        Definition constraint_solution
            {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
            (H : constraint_type g e t X C) (s : S.t) (T : type) : Prop :=
            satisfy_constraint s C /\ S.sub_type s t = T.
    End ConstraintTyping.
    
    Section PrincipalTypes.
        Definition principal_solution
            {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
            (H : constraint_type g e t X C) (s : S.t) (T : type) : Prop :=
            constraint_solution H s T /\
            forall (s' : S.t) (T' : type),
            constraint_solution H s' T' -> more_general s s'.

        Corollary unify_principal_solution :
            forall {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
                (H : constraint_type g e t X C) (s : S.t),
            unify C s ->
            principal_solution H s (S.sub_type s t).
        Proof.
            intros g e t X C H s HU.
            apply unify_principal in HU as HUC.
            unfold principal_unifier in HUC.
            unfold principal_solution.
            destruct HUC as [HSC HMG]. split.
            - unfold constraint_solution. split; auto.
            - intros s' T' Hs'T'.
                unfold constraint_solution in Hs'T'.
                destruct Hs'T' as [HSCs' HSTs']. auto.
        Qed.

        (* Interleave constraint generation and unification. 
            Should generate a principal type at each step.
            I'm not sure this is right... *)
        Inductive interleave (g : gamma) : expr -> type -> names -> Prop :=
            | il_unit : interleave g EUnit TUnit IS.empty
            | il_var : 
                forall (x : id) (p : poly) (t : type) 
                    (N : names) (C : constraint) (s : S.t),
                tget x g = Some p ->
                sub_poly_type g S.empty p t N C ->
                interleave g (EVar x) t N
            | il_fun :
                forall (x : id) (t1 t2 : type) (e : expr) (N : names),
                interleave (tbind x (PType t1) g) e t2 N ->
                interleave g (EFun x t1 e) (TFun t1 t2) N
            | il_app :
                forall (e1 e2 : expr) (t1 t2 : type) 
                    (X : id) (s : S.t) (N1 N2 : names),
                interleave g e1 t1 N1 ->
                interleave g e2 t2 N2 ->
                IS.Empty (IS.inter N1 N2) ->
                IS.Empty (IS.inter N1 (fv t2)) ->
                IS.Empty (IS.inter N2 (fv t1)) ->
                ~ IS.In X N1 -> ~ IS.In X N2 ->
                ~ TIn X t1 -> ~ TIn X t2 ->
                ~ EIn X e1 -> ~ EIn X e2 -> ~ GIn X g ->
                unify [(t1, TFun t2 (TVar X))] s ->
                interleave g (EApp e1 e2) (S.sub_type s (TVar X)) (IS.union N1 N2)
            | il_let :
                forall (x : id) (e1 e2 : expr) (t1 t2 : type)
                (p1 : poly) (N1 N2 : names),
                interleave g e1 t1 N1 ->
                generalize_names g t1 p1 ->
                interleave (tbind x p1 g) e2 t2 N2 ->
                IS.Empty (IS.inter N1 N2) ->
                IS.Empty (IS.inter N1 (fv t2)) ->
                IS.Empty (IS.inter N2 (fv t1)) ->
                interleave g (ELet x e1 e2) t2 (IS.union N1 N2).

        Proposition interleave_sound :
            forall (g : gamma) (e : expr) (t : type) (N : names),
            interleave g e t N ->
            forall (C : constraint)
                (H : constraint_type g e t N C),
            exists (s : S.t), unify C s /\ constraint_solution H s t.
        Proof.
            intros g e t N HIL C H.
            induction HIL; inv H.
            - exists tempty. repeat split; 
                auto; constructor.
            - admit.
            - pose proof IHHIL H6 as IH.
                destruct IH as [s [HUs [HCS1 HCS2]]].
                exists s. repeat split; auto.
                simpl. rewrite HCS2.
                (* again, induction or
                    induction hypothesis
                    seems wrong... *)
                admit.
            - admit.
            - admit.
        Admitted.
    End PrincipalTypes.

    (* There are no good, concise explanations...
        hopefully this is correct. *)
    Section AlgorithmW.
        Inductive W (g : gamma) : expr -> type -> S.t -> names -> Prop :=
            | w_unit : W g EUnit TUnit S.empty IS.empty
            | w_var : 
                forall (x : id) (p : poly) (t : type) 
                (N : names) (C : constraint),
                tget x g = Some p ->
                sub_poly_type g S.empty p t N C ->
                W g (EVar x) t S.empty N
            | w_fun :
                forall (x : id) (t1 t2 : type) (e : expr) 
                    (N : names) (s : S.t),
                W (tbind x (PType t1) g) e t2 s N ->
                W g (EFun x t1 e) (TFun (S.sub_type s t1) t2) s N
            | w_app :
                forall (e1 e2 : expr) (t1 t2 : type) (X : id) 
                    (s1 s2 s : S.t) (N1 N2 : names),
                W g e1 t1 s1 N1 ->
                W (sub_gamma s1 g) e2 t2 s2 N2 ->
                IS.Empty (IS.inter N1 N2) ->
                IS.Empty (IS.inter N1 (fv t2)) ->
                IS.Empty (IS.inter N2 (fv t1)) ->
                ~ IS.In X N1 -> ~ IS.In X N2 ->
                ~ TIn X t1 -> ~ TIn X t2 ->
                ~ EIn X e1 -> ~ EIn X e2 -> ~ GIn X g ->
                unify [(S.sub_type s2 t1, TFun t2 (TVar X))] s ->
                W g (EApp e1 e2) (S.sub_type s (TVar X))
                    (S.compose (S.compose s1 s2) s) (IS.union N1 N2)
            | w_let :
                forall (x : id) (e1 e2 : expr) (t1 t2 : type)
                    (p1 : poly) (s1 s2 : S.t) (N1 N2 : names),
                W g e1 t1 s1 N1 ->
                generalize_names g (S.sub_type s1 t1) p1 ->
                W (tbind x p1 (sub_gamma s1 g)) e2 t2 s2 N2 ->
                IS.Empty (IS.inter N1 N2) ->
                IS.Empty (IS.inter N1 (fv t2)) ->
                IS.Empty (IS.inter N2 (fv t1)) ->
                W g (ELet x e1 e2) t2 s2 N2.

    (* uggghhhh... *)
    Proposition W_soundish:
        forall (g : gamma) (e : expr) (t : type) (s : S.t) (N : names),
        W g e t s N ->
        exists (C : constraint),
        constraint_type g e t N C.
    Proof.
        intros g e t s N HW.
        induction HW.
        - exists []. constructor.
        - exists C. apply ct_var 
            with (p := p); assumption.
        - destruct IHHW as [C HCT].
            exists C.
            remember (S.sub_type s t1) as t1' in *.
            (* apply ct_fun. *)
    Admitted.
    End AlgorithmW.
End Polymorphic.
