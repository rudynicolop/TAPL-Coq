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

Inductive type : Type :=
    | TUnit
    | TVar (X : id)
    | TFun (t1 t2 : type).

Inductive expr : Type :=
    | EUnit
    | EVar (x : id)
    | EFun (x : id) (t : type) (e : expr)
    | EApp (e1 e2 : expr).

Section Gamma.
    Definition gamma := id -> option type.

    Definition empty : gamma := fun x => None.

    Definition bind (x : id) (t : type) (g : gamma) : gamma :=
        fun y => if (x =? y)%string then Some t else g y.

    Lemma bind_correct : 
        forall (x : id) (t : type) (g : gamma),
        bind x t g x = Some t.
    Proof.
        intros. unfold bind. destruct ((x =? x)%string) eqn:eq.
        - reflexivity.
        - apply eqb_neq in eq. contradiction.
    Qed. 

    Lemma bind_complete :
        forall (x x' : id) (t t' : type),
        x' <> x -> 
        forall (g : gamma),
        (g x = Some t <-> bind x' t' g x = Some t). 
    Proof.
        intros. unfold bind. apply eqb_neq in H. 
        rewrite H. split; intros; apply H0.
    Qed.

    Lemma rebind_correct : 
        forall (x : id) (t t' : type) (g : gamma),
        bind x t g = bind x t (bind x t' g).
    Proof.
        intros. apply functional_extensionality. intros y.
        unfold bind. destruct ((x =? y)%string); reflexivity.
    Qed.

    Lemma bind_diff_comm : 
        forall (x y : id) (u v : type) (g : gamma),
        x <> y ->
        bind x u (bind y v g) = bind y v (bind x u g).
    Proof.
        intros. apply functional_extensionality. intros z.
        unfold bind. destruct ((x =? z)%string) eqn:eq.
            - apply eqb_eq in eq; subst.
                destruct ((y =? z)%string) eqn:eeq.
                + apply eqb_eq in eeq; subst. contradiction.
                + reflexivity.
            - apply eqb_neq in eq. destruct ((y =? z)%string) eqn:eeq; reflexivity.
    Qed.
End Gamma.

Section TypeCheck.
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
    Definition sigma : Type := id -> option type.

    Definition sempty : sigma := fun _ => None.

    Definition sbind (X : id) (t : type) (s : sigma) : sigma :=
        fun Y => if (X =? Y)%string then Some t else s Y.

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
End TypeSubstitution.

Definition solution (g : gamma) (e : expr) (s : sigma) (t : type) : Prop :=
    check (sub_gamma s g) (sub_expr s e) t.

Section SolutionExamples.
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
    
    Definition g : gamma := bind f (TVar X) (bind a (TVar Y) empty).
    Definition e : expr := EApp (EVar f) (EVar a).
    
    Example ex2221 : 
        solution g e (sbind X (TFun (TVar Y) TUnit) sempty) TUnit.
    Proof. ex222 (TVar Y). Qed.

    Example ex2222 :
        solution g e (sbind X (TFun (TVar Y) (TVar Z)) (sbind Z TUnit sempty)) (TVar Z).
    Proof. ex222 (TVar Y). Qed.

    Example ex2223 :
        solution g e (sbind X (TFun TUnit TUnit) (sbind Y TUnit sempty)) TUnit.
    Proof. ex222 TUnit. Qed.

    Example ex224 :
        solution g e (sbind X (TFun (TVar Y) (TVar Z)) sempty) (TVar Z).
    Proof. ex222 (TVar Y). Qed.
    
    Example ex2225 :
        solution g e (sbind X (TFun (TVar Y) (TFun TUnit TUnit)) sempty) (TFun TUnit TUnit).
    Proof. ex222 (TVar Y). Qed.

    Definition term : expr := 
        EFun x (TVar X) (EFun y (TVar Y) (EFun z (TVar Z) 
            (EApp (EApp (EVar x) (EVar z)) (EApp (EVar y) (EVar z))))).

    Example ex2231 : 
        let s := (sbind Y (TFun (TVar Z) TUnit) (sbind X (TFun (TVar Z) (TFun TUnit TUnit)) sempty)) in
        solution empty term s (sub_type s (TFun (TVar X) (TFun (TVar Y) (TFun (TVar Z) TUnit)))).
    Proof.
        unfold solution. simpl.
        repeat apply check_fun.
        apply check_app with (t1 := TUnit).
        - apply check_app with (t1 := TVar Z);
            constructor; reflexivity.
        - apply check_app with (t1 := TVar Z);
            constructor; reflexivity.
    Qed.
End SolutionExamples.

Section ConstraintTyping.
    Definition equation : Type := type * type.

    Definition constraint : Type := list equation.
    
    Definition satisfy_equation (s : sigma) (eq : equation) : Prop :=
        let (t1,t2) := eq in sub_type s t1 = sub_type s t2.
    
    Definition satisfy_constraint (s : sigma) (C : constraint) : Prop :=
        Forall (satisfy_equation s) C.
        
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
        constraint_type empty term t N C.
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
                unfold empty in Hq. discriminate.
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
                unfold empty in Hq. discriminate.
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
            unfold empty in Hq. discriminate.
    Qed.
    (* standard library lemma *)
    Axiom Forall_app : 
        forall {A : Type} (P : A -> Prop) (l1 l2 : list A),
    Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.

    Definition constraint_solution 
    {g : gamma} {e : expr} {t : type} {X : names} {C : constraint}
    (H : constraint_type g e t X C) (s : sigma) (T : type) : Prop :=
    satisfy_constraint s C /\ sub_type s t = T.

    Theorem Constraint_Typing_Soundness : 
        forall (g : gamma) (e : expr) (t : type) 
            (X : names) (C : constraint) 
            (H : constraint_type g e t X C) 
            (s : sigma) (T : type),
        constraint_solution H s T -> solution g e s T.
    Proof.
        intros g e t X C H s T HCS.
        destruct HCS as [HSC HSE].
        unfold solution. subst.
        apply substutution_preserves_typing.
        induction H; try constructor; auto. inv HSC.
        apply Forall_app in H16 as [HC1 HC2].
        apply check_app with (t1 := t2); auto.
        apply IHconstraint_type1 in HC1.
        unfold satisfy_equation in H15.
        (* maybe applying
            helper lemma too early...*)
    Admitted.  
End ConstraintTyping.

(* Definition scheme : Type := list id * type.

Definition void : scheme := (["X"],TVar "X"). *)

Inductive poly : Type :=
    | PType (t : type)
    | PForall (X : id) (t : poly).