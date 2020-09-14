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

Module Monomorphic.
    Section Syntax.
        Inductive type : Type :=
            | TUnit
            | TVar (X : id)
            | TFun (t1 t2 : type).

        Inductive expr : Type :=
            | EUnit
            | EVar (x : id)
            | EFun (x : id) (t : type) (e : expr)
            | EApp (e1 e2 : expr).

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

        (* type variable in an expression *)
        Fixpoint EIn (X : id) (e : expr) : Prop :=
            match e with
            | EUnit | EVar _ => False
            | EFun _ t e => TIn X t \/ EIn X e
            | EApp e1 e2 => EIn X e1 \/ EIn X e2
            end.
    End Syntax.

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

    Section TypeSubstitution.
        Definition sigma : Type := @tmap type.

        Fixpoint sub_type (s : sigma) (t : type) : type :=
            match t with
            | TUnit => TUnit
            | TVar X => 
                match s X with
                | None => TVar X
                | Some t' => t'
                end
            | TFun t1 t2 => TFun (sub_type s t1) (sub_type s t2)
            end.

        Lemma sub_type_empty :
            forall (t : type),
            sub_type tempty t = t.
        Proof.
            intros t. induction t; try reflexivity.
            simpl. rewrite IHt1. rewrite IHt2.
            reflexivity.
        Qed.

        Definition sub_gamma (s : sigma) (g : gamma) : gamma :=
            fun x =>
                match g x with
                | None => None
                | Some t => Some (sub_type s t)
                end.

        (* s2(s1(X)) *)
        Definition compose_sigma (s1 s2 : sigma) : sigma :=
            fun X => 
                match s1 X with
                | None => s2 X
                | Some t => Some (sub_type s2 t)
                end.

        Lemma compose_empty :
            forall (s : sigma),
            s = compose_sigma tempty s.
        Proof.
            intros s. apply functional_extensionality.
            intros x. reflexivity.
        Qed.

        Fixpoint sub_expr (s : sigma) (e : expr) : expr :=
            match e with
            | EUnit => EUnit
            | EVar x => EVar x
            | EFun x t e => EFun x (sub_type s t) (sub_expr s e)
            | EApp e1 e2 => EApp (sub_expr s e1) (sub_expr s e2)
            end.
        
        Lemma bind_sub_gamma :
            forall (s : sigma) (g : gamma) (x : id) (t : type),
            sub_gamma s (bind x t g) = bind x (sub_type s t) (sub_gamma s g).
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
            forall (s : sigma),
            check (sub_gamma s g) (sub_expr s e) (sub_type s t).
        Proof.
            intros g e t H. induction H; intros s; try constructor.
            - unfold sub_gamma. rewrite H. reflexivity.
            - fold sub_type. fold sub_expr.
                rewrite <- bind_sub_gamma.
                apply IHcheck.
            - apply check_app with (t1 := sub_type s t1);
                fold sub_expr; auto.
                specialize IHcheck1 with (s := s).
                simpl in IHcheck1. assumption.
        Qed.

        Definition solution (g : gamma) (e : expr) (s : sigma) (t : type) : Prop :=
        check (sub_gamma s g) (sub_expr s e) t.
    End TypeSubstitution.

    Section ConstraintTyping.
        Definition equation : Type := type * type.

        Definition constraint : Type := list equation.
        
        Definition satisfy_equation (s : sigma) (eq : equation) : Prop :=
            let (t1,t2) := eq in sub_type s t1 = sub_type s t2.
        
        Definition satisfy_constraint (s : sigma) (C : constraint) : Prop :=
            Forall (satisfy_equation s) C.

        (* type variable in an equation *)
        Fixpoint EQIn (X : id) (eq : equation) : Prop :=
            let (t1,t2) := eq in TIn X t1 \/ TIn X t2.

        (* type variable in a constraint *)
        Definition CIn (X : id) (C : constraint) : Prop :=
            Exists (EQIn X) C.

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

        (* standard library lemma *)
        Axiom Forall_app : 
            forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
        Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.

        Definition constraint_solution 
        {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
        (H : constraint_type g e t X C) (s : sigma) (T : type) : Prop :=
        satisfy_constraint s C /\ sub_type s t = T.

        Theorem Constraint_Typing_Sound : 
            forall (g : gamma) (e : expr) (t : type) 
                (X : names) (C : constraint) 
                (H : constraint_type g e t X C) 
                (s : sigma) (T : type),
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
                fold sub_type. fold sub_expr.
                rewrite <- bind_sub_gamma. auto.
            - inv HSC.
                apply Forall_app in H16 as [HC1 HC2].
                apply check_app with (t1 := sub_type s t2); auto.
                fold sub_expr.
                apply IHconstraint_type1 in HC1.
                unfold satisfy_equation in H15.
                rewrite H15 in HC1. simpl in HC1.
                assumption.
        Qed.

        (* s/N *)
        Definition sigma_diff (s : sigma) (N : names) : sigma := 
            fun X => if IS.mem X N then None else s X.

        Theorem Constraint_Typing_Complete : 
            forall (g : gamma) (e : expr) (t : type) 
            (X : names) (C : constraint) 
            (H : constraint_type g e t X C) 
            (s : sigma) (T : type),
            sigma_diff s X = s ->
            solution g e s T ->
            exists (s' : sigma),
            sigma_diff s' X = s /\ constraint_solution H s' T.
        Proof.
            intros g e t X C H.
            (* Coq won't let me do induction on H *)
            (* induction H. *)
        Abort.
    End ConstraintTyping.

    Section Unification.
        Definition sub_equation (s : sigma) (eq : equation) : equation :=
            let (t1,t2) := eq in (sub_type s t1, sub_type s t2).

        Definition sub_constraint (s : sigma) (C : constraint) : constraint :=
            map (sub_equation s) C.

        Inductive unify : constraint -> sigma -> Prop :=
            | unify_nil : unify [] tempty
            | unify_eq : 
                forall (t : type) (C : constraint) (s : sigma),
                unify C s ->
                unify ((t,t) :: C) s
            | unify_left_var :
                forall (X : id) (t : type) (C : constraint) (s : sigma),
                ~ TIn X t ->
                unify (sub_constraint (bind X t tempty) C) s ->
                unify ((TVar X, t) :: C) (compose_sigma (bind X t tempty) s)
            | unify_right_var :
                forall (X : id) (t : type) (C : constraint) (s : sigma),
                ~ TIn X t ->
                unify (sub_constraint (bind X t tempty) C) s ->
                unify ((t, TVar X) :: C) (compose_sigma (bind X t tempty) s)
            | unify_fun : 
                forall (a1 a2 b1 b2 : type) (C : constraint) (s : sigma),
                unify ((a1,a2) :: (b1,b2) :: C) s ->
                unify ((TFun a1 b1, TFun a2 b2) :: C) s.

        Definition more_general (s s' : sigma) : Prop :=
            exists (s'' : sigma), s' = compose_sigma s s''.

        Definition principal_unifier (C : constraint) (s : sigma) : Prop := 
            satisfy_constraint s C /\ 
            forall (s' : sigma), 
            satisfy_constraint s' C ->  more_general s s'.
        
        Lemma satisfy_equation_compose :
            forall (X : id) (t : type) (s : sigma),
            ~ TIn X t ->
            satisfy_equation (compose_sigma (bind X t tempty) s) (TVar X, t).
        Proof.
            intros X t s H.
            unfold satisfy_equation.
            unfold compose_sigma. simpl.
            rewrite bind_correct.
            (* Intuitively true. *)
            (* generalize dependent X. *)
            (* generalize dependent s. *)
            induction t; 
            (* intros s X H;  *)
            auto.
            - assert (HXX : X <> X0).
                + intros HF. apply H. subst.
                    reflexivity.
                + simpl. admit.
            - simpl in H. 
                apply CP.not_or_and in H as [H1 H2].
                apply IHt1 in H1. apply IHt2 in H2.
                simpl. rewrite H1. rewrite H2.
                (* This case makes no sense. *)
        Admitted.

        Lemma satisfy_equation_sym :
            forall (s : sigma) (t1 t2 : type),
            satisfy_equation s (t1,t2) ->
            satisfy_equation s (t2,t1).
        Proof.
            intros s t1 t2 H. 
            unfold satisfy_equation in *. auto.
        Qed.

        Lemma satisfy_constraint_compose :
            forall (s : sigma) (X : id) (t : type) (C : constraint),
            satisfy_constraint s (sub_constraint (bind X t tempty) C) ->
            satisfy_constraint (compose_sigma (bind X t tempty) s) C.
        Proof.
            intros s X t C H.
            unfold satisfy_constraint in *.
            induction C; constructor; inv H; auto.
            destruct a as [t1 t2].
            unfold satisfy_equation in *.
            simpl in H2. clear H3 IHC H.
            unfold compose_sigma.
            destruct t1; destruct t2;
            simpl in *; auto;
            try destruct (sbind X t sempty X0); 
            try destruct (sbind X t sempty X1);
            auto; try discriminate.
        Admitted.

        Theorem unify_correct :
            forall (C : constraint) (s : sigma),
            unify C s -> principal_unifier C s.
        Proof.
            intros C s HU. unfold principal_unifier.
            induction HU; split;
            try (intros s' HSC; unfold more_general).
            - constructor.
            - exists s'. apply compose_empty.
            - destruct IHHU as [HS _].
                constructor; auto.
                unfold satisfy_equation.
                reflexivity.
            - inv HSC. destruct IHHU as [_ IH].
                apply IH in H2. assumption.
            - destruct IHHU as [IH _].
                constructor.
                + apply satisfy_equation_compose. assumption.
                + apply satisfy_constraint_compose. assumption.
            - inv HSC. destruct IHHU as [_ IH]. admit.
            - destruct IHHU as [IH _].
                constructor.
                + apply satisfy_equation_sym.
                    apply satisfy_equation_compose.
                    assumption.
                + apply satisfy_constraint_compose. assumption.
            - admit.
            - destruct IHHU as [IH _]. inv IH.
                inv H2. constructor; auto.
                unfold satisfy_equation in *.
                clear H2 H4. simpl.
                rewrite H1. rewrite H3.
                reflexivity.
            - destruct IHHU as [_ IH].
                assert (H : satisfy_constraint 
                    s' ((a1, a2) :: (b1, b2) :: C)).
                + inv HSC. inv H1.
                    constructor; auto.
                + apply IH in H. assumption.
        Admitted.
    End Unification.

    Section PrincipalTypes.
        Definition principal_solution
        {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
        (H : constraint_type g e t X C) (s : sigma) (T : type) : Prop :=
        constraint_solution H s T /\
        forall (s' : sigma) (T' : type),
        constraint_solution H s' T' -> more_general s s'.

        Corollary unify_principal_solution :
            forall {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
                (H : constraint_type g e t X C) (s : sigma),
            unify C s ->
            principal_solution H s (sub_type s t).
        Proof.
            intros g e t X C H s HU.
            apply unify_correct in HU as HUC.
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
                (H : constraint_type g e t X C) (s' : sigma) (T' : type),
            constraint_solution H s' T' ->
            exists (s : sigma), unify C s.
        Proof.
            intros g e t X C H s' T' HCS.
            unfold constraint_solution in HCS.
            destruct HCS as [HSC HST].
            dependent induction H; simpl in *;
            try (exists tempty; apply unify_nil).
            - apply IHconstraint_type
                with (T' := sub_type s' t2) in HSC; auto.
            - inv HSC. apply Forall_app in H16 as [HC1 HC2].
                apply IHconstraint_type1 
                    with (T' := sub_type s' t1) in HC1; auto.
                apply IHconstraint_type2
                    with (T' := sub_type s' t2) in HC2; auto.
                destruct HC1 as [s1 HU1].
                destruct HC2 as [s2 HU2].
                destruct t1.
                + inv H15.
                + exists (compose_sigma (bind X0 (TFun t2 (TVar X)) tempty) (compose_sigma s1 s2)).
                    constructor; admit.
                + exists (compose_sigma s1 s2).
                    constructor. admit.
        Admitted.

        Theorem principal_types :
            forall {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
                (H : constraint_type g e t X C),
            (exists (s' : sigma) (T' : type), constraint_solution H s' T') ->
            exists (s : sigma) (T : type), principal_solution H s T.
        Proof.
            intros g e t X C H [s' [T' HCS]].
            apply constraint_solution_unify in HCS.
            destruct HCS as [s HU].
            exists s. exists (sub_type s t).
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
                forall (e1 e2 : expr) (t1 t2 : type) (X : id) (s : sigma),
                interleave g e1 t1 ->
                interleave g e2 t2 ->
                ~ TIn X t1 -> ~ TIn X t2 ->
                ~ EIn X e1 -> ~ EIn X e2 -> GNIn X g ->
                unify [(t1, TFun t2 (TVar X))] s ->
                interleave g (EApp e1 e2) (sub_type s (TVar X)).

        Proposition interleave_sound :
            forall (g : gamma) (e : expr) (t : type),
            interleave g e t ->
            forall (N : names) (C : constraint)
                (H : constraint_type g e t N C),
            exists (s : sigma), unify C s /\ constraint_solution H s t.
        Proof.
            intros g e t HIL. 
            induction HIL; intros N C HCT; inv HCT;
            unfold constraint_solution.
            - exists tempty. repeat split; constructor.
            - exists tempty. repeat split; 
                try constructor. apply sub_type_empty.
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
            solution g e (bind X (TFun (TVar Y) TUnit) tempty) TUnit.
        Proof. ex222 (TVar Y). Qed.

        Example ex2222 :
            solution g e (bind X (TFun (TVar Y) (TVar Z)) (bind Z TUnit tempty)) (TVar Z).
        Proof. ex222 (TVar Y). Qed.

        Example ex2223 :
            solution g e (bind X (TFun TUnit TUnit) (bind Y TUnit tempty)) TUnit.
        Proof. ex222 TUnit. Qed.

        Example ex224 :
            solution g e (bind X (TFun (TVar Y) (TVar Z)) tempty) (TVar Z).
        Proof. ex222 (TVar Y). Qed.
        
        Example ex2225 :
            solution g e (bind X (TFun (TVar Y) (TFun TUnit TUnit)) tempty) (TFun TUnit TUnit).
        Proof. ex222 (TVar Y). Qed.

        Definition term : expr := 
            EFun x (TVar X) (EFun y (TVar Y) (EFun z (TVar Z) 
                (EApp (EApp (EVar x) (EVar z)) (EApp (EVar y) (EVar z))))).

        Example ex2231 : 
            let s := (bind Y (TFun (TVar Z) TUnit) (bind X (TFun (TVar Z) (TFun TUnit TUnit)) tempty)) in
            solution tempty term s (sub_type s (TFun (TVar X) (TFun (TVar Y) (TFun (TVar Z) TUnit)))).
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
    Module M := Monomorphic.

    Definition type : Type := M.type.

    Inductive poly : Type :=
        | PType (t : type)
        | PForall (X : id) (t : poly).
End Polymorphic.