(* Coq 8.9.1 *)

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
Require Import Coq.Lists.ListDec.

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
    Lemma dec_eq : decidable_eq id.
    Proof. 
        unfold decidable_eq. intros x y.
        unfold decidable. destruct (eq_dec x y).
        - left. assumption.
        - right. assumption.
    Qed.
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

Fixpoint mem (N : list id) (X : id) : bool :=
    match N with
    | [] => false
    | Y :: N =>
        if (Y =? X)%string then true else mem N X
    end.

Lemma mem_spec :
    forall (N : list id) (X : id),
    mem N X = true <-> In X N.
Proof.
    intros N X. split; 
    induction N; intros H;
    try discriminate;
    try (inv H; contradiction).
    - simpl in H. destruct (a =? X) eqn:eq.
        + apply eqb_eq in eq. subst.
            constructor. reflexivity.
        + apply in_cons. auto.
    - destruct (IdDec.eq_dec a X) as [HI | HI];
        subst; simpl.
        + assert (X =? X = true);
            try (apply eqb_eq; reflexivity).
            rewrite H0. reflexivity.
        + inv H; try contradiction.
            apply eqb_neq in HI.
            rewrite HI. auto.
Qed.

Section IdMap.
    Context {T : Type}.

    Definition imap : Type := list (id * T).

    Definition iempty : imap := [].

    Definition ibind (x : id) (t : T) (m : imap) : imap := (x, t) :: m.

    Definition domain (m : imap) : list id := map fst m.

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

    Lemma mem_get_domain :
        forall (m : imap) (d : list id),
        incl (domain m) d ->
        forall (X : id) (t : T),
        iget X m = Some t ->
        mem d X = true.
    Proof.
        intros m d HI X r HG.
        unfold incl in HI.
        specialize HI with (a := X).
        apply mem_spec. apply HI.
        clear HI. induction m;
        try discriminate.
        simpl in *. destruct a as [Y t].
        simpl in *. destruct (Y =? X) eqn:eq; auto.
        left. apply eqb_eq. assumption.
    Qed.

    (* Sketchy but useful axioms. *)
    Axiom bind_same :
        forall (x : id) (t t' : T) (m : imap),
        ibind x t (ibind x t' m) = ibind x t m.

    Axiom bind_diff_comm :
        forall (x y : id),
        x <> y ->
        forall (t1 t2 : T) (m : imap),
        ibind x t1 (ibind y t2 m) = ibind y t2 (ibind x t1 m).
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

Definition poly : Type := list id * type.

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
    Fixpoint tcompose (s1 s2 : T) : T :=
        match s1 with
        | [] => s2
        | (X, T) :: s1 => (X, st s2 T) :: tcompose s1 s2
        end.

    Lemma compose_empty :
        forall (s : T), tcompose s [] = s.
    Proof.
        induction s; try reflexivity.
        simpl. destruct a as [X T].
        rewrite IHs. rewrite st_empty.
        reflexivity.
    Qed.

    Lemma tcompose_correct :
        forall (s1 s2 : T) (t : type),
        st (tcompose s1 s2) t = st s2 (st s1 t).
    Proof.
        intros s1 s2. induction t; 
        simpl in *; auto.
        - induction s1; auto; simpl.
            destruct a as [Y T]. simpl.
            destruct (Y =? X) eqn:eq; auto.
        - rewrite IHt1. rewrite IHt2.
            reflexivity.
    Qed.

    Fixpoint sp' (s : T) (N : list id) (t : type) :=
        match t with
        | TUnit => TUnit
        | TFun t1 t2 => TFun (sp' s N t1) (sp' s N t2)
        | TVar X =>
            if mem N X then TVar X else
                match iget X s with
                | None => TVar X
                | Some T => T
                end
        end.

    (* poly-type type substitution. *)
    Definition sp (s : T) (p : poly) : poly := 
        let (N,t) := p in (N, sp' s N t).

    Lemma sp_empty :
        forall (p : poly), sp iempty p = p.
    Proof.
        intros [N t]. unfold sp.
        induction t; simpl in *; auto.
        - destruct (mem N X); auto.
        - injintrosubst IHt1.
            injintrosubst IHt2.
            rewrite H. rewrite H0.
            reflexivity.
    Qed.

    Lemma sp'_compose :
        forall (s1 s2 : T) (N : list id) (t : type),
        sp' (tcompose s1 s2) N t = sp' s2 N (sp' s1 N t).
    Proof.
        intros s1 s2 N t. 
        induction t; simpl in *; auto.
        - destruct (mem N X) eqn:eq; simpl;
            try (rewrite eq; reflexivity).
            induction s1; simpl;
            try (rewrite eq; reflexivity).
            destruct a as [Y U]. simpl.
            destruct (Y =? X) eqn:eqyx; auto. admit.
        - rewrite IHt1. rewrite IHt2. reflexivity.
    Admitted.

    Lemma sp_compose :
        forall (s1 s2 : T) (p :poly),
        sp (tcompose s1 s2) p = sp s2 (sp s1 p).
    Proof.
        intros s1 s2 [N t]. unfold sp.
        rewrite sp'_compose. reflexivity.
    Qed.

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

    Lemma sg_compose :
        forall (s1 s2 : T) (g : gamma),
        sg (tcompose s1 s2) g = sg s2 (sg s1 g).
    Proof.
        intros s1 s2 g. induction g; auto.
        simpl. destruct a as [x p].
        rewrite IHg. rewrite sp_compose.
        reflexivity.
    Qed.

    Lemma stsp'_empty :
        forall (S : T) (t : type),
        st S t = sp' S [] t.
    Proof.
        intros S t. induction t; simpl; auto.
        rewrite IHt1. rewrite IHt2.
        reflexivity.
    Qed.

    Lemma stsp_empty :
        forall (S : T) (t : type),
        ([], st S t) = sp S ([], t).
    Proof.
        intros S t. rewrite stsp'_empty.
        reflexivity.
    Qed.

    Lemma compose_assoc :
        forall (s1 s2 s3 : T),
        tcompose s1 (tcompose s2 s3) =
            tcompose (tcompose s1 s2) s3.
    Proof.
        induction s1; 
        intros s2 s3; auto; simpl;
        destruct a as [Z t]; simpl.
        rewrite IHs1. rewrite tcompose_correct.
        reflexivity.
    Qed.
End TypeSubstitution.
Module TS := TypeSubstitution.

Module FreeVariables.
    Fixpoint fvt (t : type) : list id :=
        match t with
        | TUnit => []
        | TVar X => [X]
        | TFun t1 t2 => (fvt t1) ++ (fvt t2)
        end.

    Fixpoint fvp' (N : list id) (t : type) : list id :=
        match t with
        | TUnit => []
        | TFun t1 t2 => (fvp' N t1) ++ (fvp' N t2)
        | TVar X => 
            if mem N X then [] else [X]
        end.

    Fixpoint fvp (p : poly) : list id := fvp' (fst p) (snd p).

    Definition fvg : gamma -> list id :=
        fold_right 
            (fun (xp : id * poly) (Xs : list id) =>
                let (_,p) := xp in
                (fvp p) ++ Xs) [].

    Lemma st_notin :
        forall (X : id) (t T : type),
        ~ In X (fvt t) ->
        TS.st [(X, T)] t = t.
    Proof.
        intros X t T H. induction t; auto.
        - assert (HX : X <> X0).
            + intros H'. apply H. subst.
                repeat constructor.
            + simpl. apply eqb_neq in HX.
                rewrite HX. reflexivity.
        - simpl in *.
            assert (H12 : ~ In X (fvt t1)
                /\ ~ In X (fvt t2)); try split;
            try (intros H'; apply H; apply in_app_iff; auto).
            destruct H12 as [H1 H2].
            apply IHt1 in H1. apply IHt2 in H2.
            rewrite H1. rewrite H2. reflexivity.
    Qed.    
End FreeVariables.
Module FV := FreeVariables.

(* Type Specialization. *)
Module Specialize.
    (* bound variables N' not free in another type p *)
    Definition FPV (N' : list id) (p : poly) : Prop :=
        Forall (fun X' => ~ In X' (FV.fvp p)) N'.

    Lemma FPV_refl' :
        forall (X : id) (N : list id) (t : type),
        ~ In X (FV.fvp (X :: N, t)).
    Proof.
        intros Z N t. induction t; intros H;
        simpl; try contradiction.
        - simpl in H. destruct (Z =? X) eqn:eq.
            + inv H.
            + destruct (mem N X); inv H; auto.
                apply eqb_neq in eq. contradiction.
        - simpl in H. apply in_app_or in H as [H | H].
            + apply IHt1. unfold FV.fvp.
                simpl. assumption.
            + apply IHt2. unfold FV.fvp.
                simpl. assumption.
    Qed.

    Lemma FPV_refl :
        forall (N : list id) (t : type), FPV N (N,t).
    Proof.
        intros N t. unfold FPV.
        induction N; constructor.
        - apply FPV_refl'.
        - simpl in *. apply Forall_forall.
            pose proof Forall_forall as FF.
            pose proof FF id (fun X' : id => ~ In X' (FV.fvp' N t)) N 
                as [FF' _]; clear FF. intros X HIN.
                apply FF' with (x := X) in IHN; auto; clear FF'.
                induction t; simpl in *; intros H;
                try contradiction.
                + destruct (a =? X0) eqn:eqaX0; auto.
                + apply IHN. apply in_app_iff.
                    pose proof contrapositive as CP.
                    assert (DIN1 : decidable (In X (FV.fvp' N t1)));
                    assert (DIN2 : decidable (In X (FV.fvp' N t2)));
                    try apply In_decidable; try apply IdDec.dec_eq.
                    pose proof CP (In X (FV.fvp' N t1)) 
                        (In X (FV.fvp' (a :: N) t1)) DIN1 as [IH1 _].
                    pose proof CP (In X (FV.fvp' N t2)) 
                        (In X (FV.fvp' (a :: N) t2)) DIN2 as [IH2 _].
                    clear CP DIN1 DIN2.
                    apply in_app_iff in H as [H | H].
                    * left. apply IH1 in IHt1; auto.
                    * right. apply IH2 in IHt2; auto.
        Qed.

    (* p' <= p, p is more general than p' *)
    Definition R (p p' : poly) : Prop :=
        let (N, t) := p in
        let (N', t') := p' in
        exists (s : TS.T), 
        incl (domain s) N /\ TS.st s t = t' /\
        Forall (fun X' => ~ In X' (FV.fvp p)) N'.

    Lemma R_refl : forall (p : poly), R p p.
    Proof.
        intros [N t]. exists iempty. 
        repeat split.
        - simpl. unfold incl. intros a H. inv H.
        - apply TS.st_empty.
        - apply FPV_refl.
    Qed.

    Lemma R_trans :
        forall (a b c : poly),
        R a b -> R b c -> R a c.
    Proof.
        intros [NA a] [NB b] [NC c] 
            [s1 [Hincl1 [Hst1 HPV1]]]
            [s2 [Hincl2 [Hst2 HPV2]]].
        rewrite <- Hst1 in Hst2.
        (* rewrite <- TS.tcompose_correct in Hst2. *)
        induction a; unfold R.
        - exists (TS.tcompose s1 s2). repeat split; auto.
            + induction s1; simpl in *.
                * admit.
                * destruct a as [X t]. simpl in *.
                    admit.
    Abort.

    (* Robin, how is this true??? *)
    Lemma R_sub :
        forall (p p' : poly),
        R p p' ->
        forall (S : TS.T),
        R (TS.sp S p) (TS.sp S p').
    Proof.
        intros [N t] [N' t'] [s [HID [HS HF]]] S.
        unfold TS.sp. induction t; unfold R.
        - exists s. repeat split; auto.
            rewrite <- HS. reflexivity.
        - simpl in HS. 
            destruct (iget X s) eqn:eqg; subst.
            { exists s. repeat split; auto.
                - simpl. assert (Hmem : mem N X = true).
                    + apply mem_get_domain with
                        (m := s) (t := t'); auto.
                    + rewrite Hmem. simpl.
                        rewrite eqg.  admit.
                - admit. }
    Admitted.

    Lemma R_free_vars :
        forall (p p' : poly),
        R p p' ->
        forall (X : id),
        In X (FV.fvp p) -> In X (FV.fvp p').
    Proof.
        intros [N t].
        induction t;
        intros [N' t'] [s [H1 [H2 H3]]] Z HIn; simpl.
        - simpl in HIn. contradiction.
        - simpl in HIn. simpl in H2.
            destruct (mem N X) eqn:eqm; inv HIn.
            { destruct (iget Z s) eqn:eqg.
                - exfalso.
                    apply mem_get_domain with
                        (d := N) in eqg; auto.
                        rewrite eqm in eqg.
                        discriminate.
                - simpl in *. destruct (mem N' Z) eqn:eqm'.
                    + exfalso. pose proof 
                        Forall_forall
                        (fun X' : id =>
                            ~ In X' (if mem N Z then [] else [Z]))
                        N' as [FF _ ].
                        apply FF with (x := Z) in H3;
                            auto; clear FF.
                        * rewrite eqm in H3. apply H3.
                            repeat constructor.
                        * apply mem_spec; auto.
                    + repeat constructor. }
            { inv H. }
        - inv H2. simpl. apply in_app_iff.
            simpl in HIn. simpl in H3.
            pose proof Forall_forall
                (fun X' : id => ~ In X' (FV.fvp' N t1 ++ FV.fvp' N t2))
                N' as [FF _].
            apply in_app_iff in HIn as [H' | H'].
            + pose proof IHt1 (N',TS.st s t1) as IH.
                clear IHt1 IHt2.
                assert (HR : R (N, t1) (N', TS.st s t1)).
                * exists s. repeat split; auto.
                    apply Forall_forall.
                    intros X HInXN'.
                    simpl in H3.
                    apply FF with (x := X) in H3; clear FF; auto.
                    simpl. intros H''.
                    apply H3. apply in_app_iff. auto.
                * left. apply IH with (X := Z) in HR; auto.
            + pose proof IHt2 (N',TS.st s t2) as IH.
                clear IHt1 IHt2.
                assert (HR : R (N, t2) (N', TS.st s t2)).
                * exists s. repeat split; auto.
                    apply Forall_forall.
                    intros X HInXN'.
                    simpl in H3.
                    apply FF with (x := X) in H3; clear FF; auto.
                    simpl. intros H''.
                    apply H3. apply in_app_iff. auto.
                * right. apply IH with (X := Z) in HR; auto.
    Qed.
End Specialize.
Module SP := Specialize.

Module Inference.
    Inductive infer (g : gamma) : expr -> poly -> Prop :=
        | infer_unit : infer g EUnit ([], TUnit)
        | infer_var :
            forall (x : id) (p : poly),
            iget x g = Some p ->
            infer g (EVar x) p
        | infer_app :
            forall (e1 e2 : expr) (t t' : type),
            infer g e1 ([], (TFun t t')) ->
            infer g e2 ([], t) ->
            infer g (EApp e1 e2) ([], t')
        | infer_fun :
            forall (x : id) (e : expr) (t' t : type),
            infer (ibind x ([], t') g) e ([], t) ->
            infer g (EFun x e) ([], (TFun t' t))
        | infer_let :
            forall (x : id) (e e' : expr) (p : poly) (t : type),
            infer g e p ->
            infer (ibind x p g) e' ([], t) ->
            infer g (ELet x e e') ([], t)
        | infer_inst :
            forall (e : expr) (p p' : poly),
            SP.R p p' ->
            infer g e p ->
            infer g e p'
        | infer_gen :
            forall (e : expr) (X : id) (N : list id) (t : type),
            ~ In X (FV.fvg g) ->
            infer g e (N, t) ->
            infer g e (X :: N, t).

    Example identity_fun :
        infer iempty (EFun "x" (EVar "x")) 
            (["A"], TFun (TVar "A") (TVar "A")).
    Proof.
        apply infer_gen.
        - simpl. intros H. assumption.
        - repeat constructor.
    Qed.

    Example self_app :
        infer 
            (ibind "z" 
                (["A"], TFun (TVar "A") (TVar "A")) iempty)
            (EApp (EVar "z") (EVar "z"))
            ([], (TFun (TVar "A") (TVar "A"))).
    Proof.
        apply infer_app with 
            (t := TFun (TVar "A") (TVar "A"));
        apply infer_inst with 
            (p := (["A"], TFun (TVar "A") (TVar "A"))).
            - exists [("A", TFun (TVar "A") (TVar "A"))].
                repeat split; try constructor.
                simpl in *. destruct H; auto.
                contradiction.
            - repeat constructor.
        - exists [("A", TVar "A")]. repeat split;
            try constructor. simpl in *. 
            destruct H; auto. contradiction.
        - repeat constructor.
    Qed.

    Example let_identity_self_app :
        infer iempty
            (ELet "z" (EFun "x" (EVar "x")) 
                (EApp (EVar "z") (EVar "z")))
            ([], TFun (TVar "A") (TVar "A")).
    Proof.
        apply infer_let with 
            (p := (["A"], TFun (TVar "A") (TVar "A"))).
        - apply identity_fun.
        - apply self_app.
    Qed.

    (* This is hard to prove... *)
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
        - apply infer_app with (t := TS.sp' S [] t); auto.
        - constructor. apply IHHI.
        - apply infer_let with (p := TS.sp S p); auto.
            apply IHHI2.
        - apply infer_inst with 
            (p := TS.sp S p); auto.
            apply SP.R_sub; auto.
        - apply infer_gen.
            + admit.
                (* Robin, how is this true??? *)
            + admit.
                (* Robin, how is this true??? *)
    Admitted.

    Lemma lemma_1 :
        forall (p p' : poly),
        SP.R p p' ->
        forall (g : gamma) (x : id) (e : expr) (p0 : poly),
        infer (ibind x p' g) e p0 ->
        infer (ibind x p  g) e p0.
    Proof.
        intros p p' HR g x e p0 H.
        (* remember (ibind x p' g) as g' in *. *)
        dependent induction H; subst.
        - constructor.
        - simpl in H. destruct (x =? x0) eqn:eq.
            + injintrosubst H.
                apply infer_inst with (p := p); auto.
                constructor. simpl.
                rewrite eq. reflexivity.
            + constructor. simpl.
                rewrite eq. assumption.
        - apply infer_app with (t := t).
            + apply IHinfer1 with (p'0 := p'); auto.
            + apply IHinfer2 with (p'0 := p'); auto.
        - apply infer_fun.
            destruct (IdDec.eq_dec x0 x) as [HX | HX]; subst.
            + rewrite bind_same.
                rewrite bind_same in H.
                assumption.
            + rewrite bind_diff_comm; auto.
                apply IHinfer with (p'0 := p'); auto.
                rewrite bind_diff_comm; auto.
        - apply infer_let with (p := p0).
            + apply IHinfer1 with (p'0 := p'); auto.
            + destruct (IdDec.eq_dec x0 x) as [HX | HX]; subst.
                * rewrite bind_same.
                    rewrite bind_same in H0.
                    assumption.
                * rewrite bind_diff_comm; auto.
                    apply IHinfer2 with (p'0 := p'); auto.
                    rewrite bind_diff_comm; auto.
        - apply infer_inst with (p := p0); auto.
            apply IHinfer with (p'0 := p'); auto.
        - apply infer_gen.
            + intros HIn. apply H.
                simpl. simpl in HIn.
                apply in_app_iff.
                apply in_app_iff in HIn as [H' | H']; auto.
                left. apply SP.R_free_vars with (p := p); auto.
            + apply IHinfer with (p'0 := p'); auto.
    Qed.
End Inference.
Module I := Inference.

Module Unification.
    Inductive unify : type -> type -> TS.T -> Prop :=
        | unify_eq :
            forall (t : type),
            unify t t []
        | unify_left_var :
            forall (X : id) (t : type),
            ~ In X (FV.fvt t) ->
            unify (TVar X) t [(X, t)]
        | unify_right_var :
            forall (X : id) (t : type),
            ~ In X (FV.fvt t) ->
            unify t (TVar X) [(X, t)]
        | unify_fun :
            forall (a1 b1 a2 b2 : type) (sa sb : TS.T),
            unify a1 a2 sa ->
            unify (TS.st sa b1) (TS.st sa b2) sb ->
            unify (TFun a1 b1) (TFun a2 b2) (TS.tcompose sa sb).
    
    Proposition unify_correct :
        forall (t t' : type) (s : TS.T),
        unify t t' s -> TS.st s t = TS.st s t'.
    Proof.
        intros t t' s H. induction H; simpl; auto.
        - assert (HX : X =? X = true);
            try apply eqb_eq; try reflexivity.
            rewrite HX. symmetry.
            apply FV.st_notin; auto.
        - assert (HX : X =? X = true);
            try apply eqb_eq; try reflexivity.
            rewrite HX. apply FV.st_notin; auto.
        - rewrite TS.tcompose_correct.
            rewrite TS.tcompose_correct.
            rewrite TS.tcompose_correct.
            rewrite TS.tcompose_correct.
            rewrite IHunify1. rewrite IHunify2.
            reflexivity.
    Qed.

    Proposition unify_most_general :
        forall (t t' : type) (s : TS.T),
        TS.st s t = TS.st s t' ->
        exists (v r : TS.T),
        unify t t' v /\
        TS.st (TS.tcompose v r) t  = TS.st s t /\
        TS.st (TS.tcompose v r) t' = TS.st s t'.
    Proof.
        induction t;
        destruct t'; intros s H;
        try discriminate.
        - exists []. exists s.
            split; repeat constructor.
        - exists [(X, TUnit)]. destruct s;
            try discriminate.
            simpl in H. admit.
        - admit.
    Abort.
End Unification.
Module U := Unification.

Module AlgorithmW.
    (* free variables of t not in g *)
    Fixpoint unbound_free (g : gamma) (t : type) : list id :=
        match t with
        | TUnit => []
        | TFun t1 t2 => unbound_free g t1 ++ unbound_free g t2
        | TVar X =>
            if mem (FV.fvg g) X then [] else [X]
        end.

    Definition closure (g : gamma) (t : type) : poly := (unbound_free g t, t).

    Definition tvars : list id -> list type := map TVar.
    
    Definition empty_inter {A : Type} (l1 l2 : list A) :=
        (forall (a1 : A), In a1 l1 -> ~ In a1 l2) /\
        (forall (a2 : A), In a2 l2 -> ~ In a2 l1).

    (*
        W g e t s N, given a g and e, W gives:
        - t: an inferred type
        - s: a type substitution
        - N: used names
    *)
    Inductive W (g : gamma) : expr -> type -> TS.T -> list id -> Prop :=
        | w_unit : W g EUnit TUnit [] []
        | w_var : 
            forall (x : id) (A B : list id) (t t' : type),
            iget x g = Some (A, t) ->
            length A = length B ->
            empty_inter A B ->
            empty_inter (FV.fvt t) B ->
            TS.st (combine A (tvars B)) t = t' ->
            W g (EVar x) t' [] B
        | w_app :
            forall (e1 e2 : expr) (t1 t2 : type)
                (U : id) (s1 s2 v : TS.T) (N1 N2 N : list id),
            W g e1 t1 s1 N1 ->
            W (TS.sg s1 g) e2 t2 s2 N2 ->
            empty_inter N1 N2 ->
            ~ In U N1 -> ~ In U N2 ->
            ~ In U (FV.fvt t1) -> ~ In U (FV.fvt t2) ->
            ~ In U (FV.fvg g) ->
            U.unify (TS.st s2 t1) (TFun t2 (TVar U)) v ->
            N = U :: N1 ++ N2 ->
            W g (EApp e1 e2) (TS.st v (TVar U))
                (TS.tcompose s1 (TS.tcompose s2 v)) N
        | w_fun :
            forall (x U : id) (e : expr)
                (t : type) (s : TS.T) (N : list id),
            ~ In U N ->
            ~ In U (FV.fvg g) ->
            W (ibind x ([], TVar U) g) e t s N ->
            W g (EFun x e) (TFun (TS.st s (TVar U)) t) s N
        | w_let :
            forall (x : id) (e1 e2 : expr) (t1 t2 : type)
                (s1 s2 : TS.T) (N1 N2 N : list id),
            W g e1 t1 s1 N1 ->
            W (ibind x (TS.sp s1 (closure g t1)) (TS.sg s1 g))
                e2 t2 s2 N2 ->
            empty_inter N1 N2 ->
            N = N1 ++ N2 ->
            W g (ELet x e1 e2) t2 (TS.tcompose s1 s2) N.

    Lemma incl_combine :
        forall {A : Type}
            (N : list id) (L : list A),
        length N = length L ->
        incl (domain (combine N L)) N.
    Proof.
        intros A.
        induction N; destruct L; intros HL;
        unfold incl; intros X HX;
        simpl in *; try discriminate;
        try contradiction.
        destruct HX as [HX | HX]; auto.
        injintrosubst HL.
        apply IHN in H. right.
        apply H; auto.
    Qed.

    (*
        Probably not true...
        I was attempting to define and 
        prove a helper lemma
        for the soundness proof.
     *)
    Lemma W_closure :
        forall (g : gamma) (e : expr)
            (t : type) (s : TS.T) (N : list id),
        W g e t s N ->
        TS.sp s (closure g t) = (unbound_free g t, t).
    Proof.
        intros g e t s N HW.
        induction HW; auto.
        - rewrite TS.sp_empty. reflexivity.
        - rewrite TS.sp_compose.
            rewrite TS.sp_compose.
            apply U.unify_correct in H5.
    Abort.

    Theorem WSound' :
        forall (g : gamma) (e : expr)
            (t : type) (s : TS.T) (N : list id),
        W g e t s N ->
        exists (p : poly),
        I.infer (TS.sg s g) e p /\ SP.R p ([], t).
    Proof.
        intros g e t s N HW. induction HW.
        - rewrite TS.sg_empty.
            exists ([], TUnit).
            repeat constructor.
            apply SP.R_refl.
        - rewrite TS.sg_empty.
            exists (A, t).
            repeat constructor; auto.
            exists (combine A (tvars B)).
            repeat constructor; auto.
            assert (HL : length A = length (tvars B)).
            + unfold tvars.
                rewrite map_length. assumption.
            + apply incl_combine; auto.
        - apply U.unify_correct in H5.
            destruct IHHW1 as [p1 [HF1 HR1]].
            destruct IHHW2 as [p2 [HF2 HR2]].
            exists ([], TS.st v (TVar U)).
            repeat constructor;
            try apply SP.R_refl.
            apply I.infer_app with (t := TS.st v t2).
            + simpl. simpl in H5. rewrite <- H5.
                rewrite <- TS.tcompose_correct.
                rewrite TS.stsp_empty.
                rewrite TS.sg_compose.
                apply I.infer_sub.
                apply I.infer_inst with (p := p1); auto.
            + rewrite TS.compose_assoc.
                rewrite TS.sg_compose.
                rewrite TS.stsp_empty.
                apply I.infer_sub.
                rewrite TS.sg_compose.
                apply I.infer_inst with (p := p2); auto.
        - destruct IHHW as [p [HF HR]].
            exists ([], TFun (TS.st s (TVar U)) t).
            repeat constructor; try apply SP.R_refl.
            apply I.infer_inst with (p := p); auto.
        - rewrite TS.sg_compose.
            destruct IHHW1 as [p1 [HF1 HR1]].
            destruct IHHW2 as [p2 [HF2 HR2]].
            exists ([], t2).
            split; try apply SP.R_refl.
            apply I.infer_let with
                (p := TS.sp s2 (TS.sp s1 (closure g t1))).
            + apply I.infer_sub.
                apply I.infer_inst with (p := p1); auto.
                destruct p1 as [X1 T1].
                destruct HR1 as [s1' [HD [HS1 HFA1]]].
                exists s1'. repeat split; auto.
                * admit.
                * admit.
                (* same problem... *)
            + apply I.infer_inst with (p := p2); auto.
    Admitted.
    
    Theorem WSound : 
        forall (g : gamma) (e : expr)
            (t : type) (s : TS.T) (N : list id),
        W g e t s N -> I.infer (TS.sg s g) e ([], t).
    Proof.
        intros g e t s N HW.
        induction HW.
        - constructor.
        - rewrite TS.sg_empty.
            apply I.infer_inst with (p := (A, t)).
            + exists (combine A (tvars B)).
                repeat split; auto.
                assert (HL : length A = length (tvars B)).
                * unfold tvars. rewrite map_length.
                    assumption.
                * apply incl_combine; auto.
            + constructor. assumption.
        - apply U.unify_correct in H5.
            simpl in *. apply I.infer_app with (t := TS.st v t2).
                + rewrite <- H5. rewrite <- TS.tcompose_correct.
                    rewrite TS.stsp_empty. rewrite TS.sg_compose.
                    apply I.infer_sub; auto.
                + rewrite TS.compose_assoc.
                    rewrite TS.sg_compose.
                    rewrite TS.stsp_empty.
                    apply I.infer_sub.
                    rewrite TS.sg_compose.
                    assumption.
        - constructor; auto.
        - rewrite TS.sg_compose.
            apply I.infer_let with
                (p := TS.sp s2 (TS.sp s1 (closure g t1)));
                auto. apply I.infer_sub. admit.
                (* Induction hypothesis too restrictive. *)
    Admitted.
End AlgorithmW.
