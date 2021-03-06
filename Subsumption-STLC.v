(* Coq 8.9.1 *)

(* An extended STLC with subtyping via the Subsumption Rule *)

Require Import String.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.MSets.MSetWeakList.
Module WS := Coq.MSets.MSetWeakList.
Require Coq.MSets.MSetFacts.
Module MSF := Coq.MSets.MSetFacts.
Require Coq.Structures.Equalities.
Module SE := Coq.Structures.Equalities.
Require Import Coq.Logic.Decidable.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.JMeq.
Require Import Coq.Program.Wf.
Require Import Coq.omega.Omega.

Ltac inv H := inversion H; subst.

Ltac injintrosubst H := injection H; intros; subst.

Section Miscellaneous.
    (* Lemma from the List Library : 
        maybe I should update my Coq version... *)
    Axiom map_eq_cons : forall {A B : Type} (f : A -> B) l l' b,
        map f l = b :: l' -> 
        exists a tl, l = a :: tl /\ f a = b /\ map f tl = l'.

    Lemma in_exists_cons : 
        forall {U : Type} (u : U) (us : list U),
        In u us ->
        exists (u' : U) (us' : list U),
        us = u' :: us'.
    Proof.
        intros U u us Hinuus. destruct us.
        - inv Hinuus.
        - exists u0. exists us. reflexivity.
    Qed.

    Lemma in_cons_exists_elem :
        forall {U : Type} (u : U) (us : list U),
        exists (u' : U), In u' (u :: us).
    Proof.
        intros U u us. exists u. apply in_eq.
    Qed.

    Definition map_pair {A B C D : Type} 
    (f : A -> C) (g : B -> D) (p : A * B) : C * D := 
        match p with
        | (a,b) => (f a, g b)
        end.

    Definition ID {X : Type} (x : X) := x.

    Definition map_fst {A B C : Type} (f : A -> C) : A * B -> C * B := 
        map_pair f ID.

    Definition map_snd {A B C : Type} (f : B -> C) : A * B -> A * C := 
        map_pair ID f.  
End Miscellaneous.

Definition id := string.

Section Gamma.
    Context {T : Type}.

    Definition gamma := string -> option T.

    Definition empty : gamma := fun x => None.

    Definition bind (x : string) (t : T) (g : gamma) : gamma :=
        fun y => if String.eqb x y then Some t else g y.

    Lemma bind_correct : 
        forall (x : id) (t : T) (g : gamma),
        bind x t g x = Some t.
    Proof.
        intros. unfold bind. destruct ((x =? x)%string) eqn:eq.
        - reflexivity.
        - apply eqb_neq in eq. contradiction.
    Qed. 

    Lemma bind_complete :
        forall (x x' : id) (t t' : T) (g : gamma),
        x' <> x -> (g x = Some t <-> bind x' t' g x = Some t). 
    Proof.
        intros. unfold bind. apply eqb_neq in H. 
        rewrite H. split; intros; apply H0.
    Qed.

    Lemma rebind_correct : 
        forall (x : id) (t t' : T) (g : gamma),
        bind x t g = bind x t (bind x t' g).
    Proof.
        intros. apply functional_extensionality. intros y.
        unfold bind. destruct ((x =? y)%string); reflexivity.
    Qed.

    Lemma bind_diff_comm : 
        forall (x y : id) (u v : T) (g : gamma),
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

Section Fields.
    Definition field (t : Type) : Type := id * t.

    Definition fields (t : Type) : Type := list (field t).

    Definition predf {U : Type} (P : U -> Prop) (f : field U) : Prop := 
        P (snd f).

    Definition predf_prop {U : Type} {V : Prop} (P : U -> V) (f : field U) : V :=
        P (snd f).

    Definition predfs {U : Type} (P : U -> Prop) : fields U -> Prop := 
        Forall (predf P).

    Definition perm {U : Type} (u1 : fields U) (u2 : fields U) : Prop :=
        Permutation u1 u2.

    Definition relf {U V : Type} (R : U -> V -> Prop) (u : field U) (v : field V) : Prop :=
        (fst u) = (fst v) /\ R (snd u) (snd v).

    Definition relfs {U V : Type} (R : U -> V -> Prop) : fields U -> fields V -> Prop :=
        Forall2 (relf R).

    (* Coq doesn't let me use this but it would be helpful. *)
    Fixpoint fields_pred_ind {U : Type} {P : U -> Prop}
    (Q : forall (u : U), P u)
    (us : fields U) : predfs P us :=
        match us as us' return (predfs P us') with
        | [] => Forall_nil (predf P)
        | h :: t => Forall_cons h
            (Q (snd h))
            (fields_pred_ind Q t)
        end.

    Definition relf_pred {U V : Type} 
    {R1 : U -> V -> Prop} {R2 : U -> V -> Prop}
    {u : field U} {v : field V}
    (Q : forall (u' : U) (v' : V), R1 u' v' -> R2 u' v')
    (H : relf R1 u v) :=
        match H with
        | conj Hname HR1 => conj Hname (Q (snd u) (snd v) HR1)
        end.

    (* record field names must be unique *)
    Definition nodupfs {U : Type} (us : fields U) : Prop :=
        NoDup (map fst us).

    Lemma relfs_name_share :
        forall {U V : Type} (R : U -> V -> Prop)
        (us : fields U) (vs : fields V) (x : id),
        relfs R us vs ->
        In x (map fst us) <-> In x (map fst vs).
    Proof.
        intros U V R us vs x HR. 
        induction HR; split; intros HI; inv HI;
        destruct x0 as [x0 ux0]; destruct y as [y vy];
        destruct H as [Hfst Hr]; simpl in *; subst;
        try (left; reflexivity);
        destruct HI as [HYX | HXIN];
        try (left; assumption);
        try (right; apply IHHR; assumption).
    Qed.

    Lemma relfs_in_fst :
        forall {U : Type} (us : fields U) (x : id) (u : U),
        In (x, u) us -> In x (map fst us).
    Proof.
        intros U us x u H. induction us; inv H;
        simpl in *.
        - left. reflexivity.
        - destruct a as [a au]; simpl in *.
            destruct H as [H | H].
            + injintrosubst H. left. reflexivity.
            + right. auto.
    Qed.

    Lemma relfs_nodup_eq :
        forall {U : Type} (us : fields U) (x : id) (u1 u2 : U),
        nodupfs us -> 
        In (x,u1) us -> In (x,u2) us -> u1 = u2.
    Proof.
        intros U us x u1 u2 ND H1 H2.
        induction us; inv H1; inv H2; inv ND.
        - injintrosubst H. reflexivity.
        - apply IHus; auto. exfalso.
            apply H4. apply relfs_in_fst in H. assumption.
        - apply IHus; auto. exfalso.
            apply H4. apply relfs_in_fst in H. assumption.
        - apply IHus; auto.
    Qed.

    Lemma relfs_app :
        forall {U V : Type} (R : U -> V -> Prop) 
        (us1 us2 : fields U) (vs : fields V),
        relfs R (us1 ++ us2) vs ->
        exists (vs1 vs2 : fields V),
        vs = vs1 ++ vs2 /\
        relfs R us1 vs1 /\ relfs R us2 vs2.
    Proof.
        intros U V R us1 us2 vs HR.
        apply Forall2_app_inv_l in HR.
        destruct HR as [vs1 [vs2 [H1 [H2 Hvs]]]].
        exists vs1. exists vs2. auto.
    Qed.

    Lemma relfs_app_dist :
        forall {U V : Type} (R : U -> V -> Prop)
        (us1 us2 : fields U) (vs1 vs2 : fields V),
        relfs R us1 vs1 -> relfs R us2 vs2 ->
        relfs R (us1 ++ us2) (vs1 ++ vs2).
    Proof.
        intros U V R us1 us2 vs1 vs2 HR1 HR2.
        apply Forall2_app; auto.
    Qed.

    Lemma relfs_in_exists_r :
        forall {U V : Type} (R : U -> V -> Prop)
        (us : fields U) (vs : fields V) (v : field V),
        In v vs ->
        relfs R us vs ->
        exists (u : field U), In u us /\
        relf R u v.
    Proof.
        intros U V R us vs v Hinvs HRusvs.
        induction HRusvs; inv Hinvs.
        - exists x. split; auto.
            apply in_eq.
        - apply IHHRusvs in H0 as [u [Hinl HRuv]].
            exists u. split; auto.
            apply in_cons; auto.
    Qed.

    Lemma relfs_in_exists_l :
        forall {U V : Type} (R : U -> V -> Prop)
        (us : fields U) (vs : fields V) (u : field U),
        In u us ->
        relfs R us vs ->
        exists (v : field V), In v vs /\
        relf R u v.
    Proof.
        intros U V R us vs u Hinus HRusvs.
        induction HRusvs; inv Hinus.
        - exists y. split; auto.
            apply in_eq.
        - apply IHHRusvs in H0 as [v [Hinl HRuv]].
            exists v. split; auto.
            apply in_cons; auto.
    Qed.
End Fields.

Module Type StructEq <: SE.DecidableType.
    Import SE.
    Require Import RelationClasses.
    Parameter t : Type.
    Definition eq (a b : t) := a = b.
    Declare Instance eq_equiv : Equivalence eq.
    Axiom eq_dec : forall (a b : t),
        {a = b} + {a <> b}.
    Axiom eq_refl : forall (a : t), a = a.
    Axiom eq_sym : forall (a b : t),
        a = b -> b = a.
    Axiom eq_trans : forall (a b c : t),
        a = b -> b = c -> a = c.
End StructEq.


Module FieldDec (E : StructEq) <: StructEq.
    Import SE.
    Require Import RelationClasses.
    Definition t := field E.t.
    Definition eq (f1 f2 : t) := f1 = f2.
    Declare Instance eq_equiv : Equivalence eq.
    Theorem eq_dec : forall (f1 f2 : t),
        {f1 = f2} + {f1 <> f2}.
    Proof.
        intros [x1 f1] [x2 f2].
        destruct (IdDec.eq_dec x1 x2) as [HX | HX];
        destruct (E.eq_dec f1 f2) as [HFD | HFD]; subst;
        try (right; intros HF; injintrosubst HF; contradiction).
        left. reflexivity.
    Qed.
    Theorem eq_refl : forall (f : t), f = f.
    Proof. intros f. reflexivity. Qed.
    Theorem eq_sym : forall (f1 f2 : t),
        f1 = f2 -> f2 = f1.
    Proof. intros. subst. reflexivity. Qed.
    Theorem eq_trans : forall (f1 f2 f3 : t),
        f1 = f2 -> f2 = f3 -> f1 = f3.
    Proof. intros. subst. reflexivity. Qed.
End FieldDec.

Module SubsumptionSTLC.
    Module SSType.
        Inductive type : Type :=
            | TTop
            | TUnit
            | TFun (t t' : type)
            | TRec (fs : fields type).

        Definition fields_type := fields type.

        (* Doesn't work because Coq's Scheme Command is stupid :
            To use Scheme the Types must be mutually defined 
            with the "with" keyword. *)
        Fail Scheme type_rec' := Induction for type Sort Type
            with fields_type_rec := Induction for fields_type Sort Type.

        (* custom induction principle for Type type *)
        Section TypeInduction.
            Variable P : type -> Prop.

            Hypothesis HTop : P TTop.

            Hypothesis HUnit : P TUnit.

            Hypothesis HFun : forall (t t' : type),
                P t -> P t' -> P (TFun t t').

            Hypothesis HRec : forall (fs : fields type),
                predfs P fs -> P (TRec fs).

            Fixpoint IHType (t : type) : P t :=
                match t as ty return P ty with 
                | TTop => HTop
                | TUnit => HUnit
                | TFun t1 t2 => HFun t1 t2 (IHType t1) (IHType t2)
                | TRec fs =>
                    let fix list_ih (fs' : fields type) : predfs P fs' :=
                        match fs' as fs_ty return predfs P fs_ty with
                        | [] => Forall_nil (predf P)
                        | hf :: tf => Forall_cons hf (IHType (snd hf)) (list_ih tf)
                        end in
                    HRec fs (list_ih fs)
                end.
        End TypeInduction.

        Ltac indtype t := induction t using IHType.

        Module TypeDec <: StructEq.
            Import SE.
            Require Import RelationClasses.
            Definition t := type.
            Definition eq (t1 t2 : t) := t1 = t2.
            Declare Instance eq_equiv : Equivalence eq.
            Fixpoint eq_dec (t1 t2 : t) :
                {t1 = t2} + {t1 <> t2}.
            Proof.
                destruct t1; destruct t2;
                try (left; reflexivity);
                try (right; intros HF; discriminate).
                - specialize eq_dec with 
                    (t1 := t1_1) (t2 := t2_1) as H1.
                    specialize eq_dec with 
                        (t1 := t1_2) (t2 := t2_2) as H2.
                    destruct H1 as [H1 | H1];
                    destruct H2 as [H2 | H2]; subst;
                    try (right; intros HF; inv HF;
                        contradiction).
                    left. reflexivity.
                - generalize dependent fs0.
                    induction fs; intros gs;
                    destruct gs.
                    + left. reflexivity.
                    + right. intros HF. inv HF.
                    + right. intros HF. inv HF.
                    + destruct (IdDec.eq_dec (fst a) (fst f))
                        as [Hfst | Hfst];
                        destruct (eq_dec (snd a) (snd f)) 
                            as [HAF | HAF];
                        destruct (IHfs gs) as [IH | IH];
                        try (right; intros HF; inv HF;
                            contradiction).
                        left. inv IH. destruct a.
                        destruct f. simpl in *.
                        subst. reflexivity.
            Admitted.
            Theorem eq_refl : forall (u : t), u = u.
            Proof. intros. reflexivity. Qed.
            Theorem eq_sym : forall (u v : t), u = v -> v = u.
            Proof. unfold eq. intros; subst; reflexivity. Qed.
            Theorem eq_trans : forall (s u v : t), s = u -> u = v -> s = v.
            Proof. intros; subst. reflexivity. Qed.
        End TypeDec.

        Module TypeFieldDec := FieldDec(TypeDec).

        Fixpoint type_nat (t : type) : nat :=
            match t with
            | TTop | TUnit => 1
            | TFun t1 t2 => S ((type_nat t1) + (type_nat t2))
            | TRec ts =>
                S (fold_right (fun t' n => type_nat (snd t') + n) 0 ts)
            end.

        Lemma type_nat_pos :
            forall (t : type),
            exists (n : nat),
            type_nat t = S n.
        Proof.
            intros t. destruct t.
            - exists 0. reflexivity.
            - exists 0. reflexivity.
            - simpl. exists (type_nat t1 + type_nat t2).
                reflexivity.
            - simpl. exists 
                (fold_right
                    (fun (t' : id * type) (n0 : nat) =>
                    type_nat (snd t') + n0) 0 fs).
                reflexivity.
        Qed.
    End SSType.
    Export SSType.

    (* The Subtyping Relation *)
    Inductive subtype : type -> type -> Prop :=
        | st_refl : forall (t : type), 
            subtype t t
        | st_trans : forall (t u v : type),
            subtype t u -> 
            subtype u v ->
            subtype t v
        | st_top : forall (t : type),
            subtype t TTop
        | st_fun : forall (u u' v v' : type),
            subtype u' u ->
            subtype v v' ->
            subtype (TFun u v) (TFun u' v')
        | st_rec_width : forall (us vs : fields type),
            subtype (TRec (us ++ vs)) (TRec us)
        | st_rec_depth : forall (us vs : fields type),
            relfs subtype us vs ->
            subtype (TRec us) (TRec vs)
        | st_rec_perm : forall (us vs : fields type),
            perm us vs ->
            subtype (TRec us) (TRec vs).

    Section SubtypeInduction.
        Variable P : type -> type -> Prop.

        Hypothesis HRefl : forall (t : type), P t t.

        Hypothesis HTrans : forall (t u v : type),
            subtype t u -> P t u ->
            subtype u v -> P u v -> P t v.

        Hypothesis HTop : forall (t : type), P t TTop.

        Hypothesis HFun : forall (u u' v v' : type),
            subtype u' u -> P u' u ->
            subtype v v' -> P v v' ->
            P (TFun u v) (TFun u' v').

        Hypothesis HRecWidth : forall (us vs : fields type),
            P (TRec (us ++ vs)) (TRec us).

        Hypothesis HRecDepth : forall (us vs : fields type),
            relfs subtype us vs -> relfs P us vs ->
            P (TRec us) (TRec vs).

        Hypothesis HRecPerm : forall (us vs : fields type),
            perm us vs -> P (TRec us) (TRec vs).
        
        Fixpoint IHSubtype (t t' : type) (HS : subtype t t') {struct HS} : P t t' :=
            match HS in (subtype w w') return (P w w') with
            | st_refl t => HRefl t
            | st_trans t u v Htu Huv =>
                HTrans t u v Htu (IHSubtype t u Htu) Huv (IHSubtype u v Huv)
            | st_top t => HTop t
            | st_fun u u' v v' Hu Hv =>
                HFun u u' v v' Hu (IHSubtype u' u Hu) Hv (IHSubtype v v' Hv)
            | st_rec_width us vs => HRecWidth us vs
            | st_rec_depth us vs HRs =>
                let fix depth_helper {us' : fields type} {vs' : fields type}
                    (HRs' : relfs subtype us' vs') : Forall2 (relf P) us' vs' :=
                    match HRs' in (Forall2 _ lu lv) 
                        return (Forall2 (relf P) lu lv) with
                    | Forall2_nil _ => Forall2_nil (relf P)
                    | Forall2_cons u v Huv Husvs =>
                        Forall2_cons
                            u v (relf_pred IHSubtype Huv) 
                            (depth_helper Husvs)
                    end in
                HRecDepth us vs HRs (depth_helper HRs) 
            | st_rec_perm us vs HP => HRecPerm us vs HP
            end.
    End SubtypeInduction.

    Lemma subtype_inv_trans :
        forall (s t : type),
        subtype s t ->
        exists (u : type),
        subtype s u /\ subtype u t.
    Proof.
        intros s t HS. exists s.
        split; auto. constructor.
    Qed.

    Lemma st_fields_refl :
        forall (fs : fields type), relfs subtype fs fs.
    Proof. induction fs; constructor.
        - split; constructor.
        - assumption.
    Qed.

    Lemma st_fields_rec :
        forall (us vs : fields type),
        relfs subtype us vs -> subtype (TRec us) (TRec vs).
    Proof.
        intros us vs HS. constructor. assumption.
    Qed.

    Lemma st_app_flip : forall (us vs : fields type),
        subtype (TRec (vs ++ us)) (TRec us).
    Proof.
        intros us vs. 
        apply st_trans with (u := TRec (us ++ vs)).
        - apply st_rec_perm. apply Permutation_app_comm.
        - apply st_rec_width.
    Qed.

    Example record_subtyping_makes_sense :
        subtype 
            (TRec [("x",TUnit);("y",TUnit)]) 
            (TRec [("y",TTop)]).
    Proof.
        apply st_trans with (u := TRec [("y",TUnit)]).
        - apply st_trans with (u := TRec [("y", TUnit); ("x", TUnit)]).
            + apply st_rec_perm. constructor.
            + assert (HE : [("y", TUnit); ("x", TUnit)] 
                = [("y", TUnit)] ++ [("x", TUnit)]);
                try reflexivity. rewrite HE.
                apply st_rec_width.
        - apply st_rec_depth. constructor.
            + split; auto. apply st_top.
            + constructor.
    Qed.

    Module SSExpr.
        Inductive expr : Type :=
            | EUnit
            | EVar (x : id)
            | EFun (x : id) (t : type) (e : expr)
            | EApp (e1 e2 : expr)
            | ERec (fs : fields expr)
            | EPrj (e : expr) (x : id).

        (* custom induction principle for Type expr *)
        Section ExprInduction.
            Variable P : expr -> Prop.

            Hypothesis HUnit : P EUnit.

            Hypothesis HVar : forall (x : id), P (EVar x).

            Hypothesis HFun : forall (x : id) (t : type) (e : expr),
                P e -> P (EFun x t e).

            Hypothesis HApp : forall (e1 e2 : expr),
                P e1 -> P e2 -> P (EApp e1 e2).

            Hypothesis HRec : forall (fs : fields expr),
                predfs P fs -> P (ERec fs).

            Hypothesis HPrj : forall (e : expr) (x : id),
                P e -> P (EPrj e x).

            Fixpoint IHExpr (e : expr) : P e :=
                match e as ee return (P ee) with
                | EUnit => HUnit
                | EVar x => HVar x
                | EFun x t e => HFun x t e (IHExpr e)
                | EApp e1 e2 => HApp e1 e2 (IHExpr e1) (IHExpr e2)
                | ERec fs =>
                    let fix rec_help (fs' : fields expr) : predfs P fs' :=
                        match fs' as fs'' return (predfs P fs'') with
                        | [] => Forall_nil (predf P)
                        | hf::tf => Forall_cons hf (IHExpr (snd hf)) (rec_help tf)
                        end in
                    HRec fs (rec_help fs)
                | EPrj e x => HPrj e x (IHExpr e)
                end.
        End ExprInduction.

        Ltac indexpr e := induction e using IHExpr.

        Module ExprDec <: StructEq.
            Import SE.
            Require Import RelationClasses.
            Definition t := expr.
            Definition eq (e1 e2 : t) := e1 = e2.
            Declare Instance eq_equiv : Equivalence eq.
            Fixpoint eq_dec (e1 e2 : t) :
                {e1 = e2} + {e1 <> e2}.
            Proof.
                destruct e1; destruct e2;
                try (left; reflexivity);
                try (right; intros HF; discriminate).
                - destruct (IdDec.eq_dec x x0) as [Hxx0 | Hxx0]; subst;
                    try (left; reflexivity).
                    right. intros HF. inv HF.
                    contradiction.
                - specialize eq_dec with 
                    (e1 := e1) (e2 := e2) as HE.
                    specialize TypeDec.eq_dec with 
                        (t1 := t0) (t2 := t1) as HT.
                    specialize IdDec.eq_dec with
                        (x1 := x) (x2 := x0) as HX.
                    destruct HE as [HE | HE];
                    destruct HT as [HT | HT]; 
                    destruct HX as [HX | HX]; subst;
                    try (right; intros HF; inv HF;
                        contradiction).
                    left. reflexivity.
                - specialize eq_dec with 
                    (e1 := e1_1) (e2 := e2_1) as H1.
                    specialize eq_dec with
                    (e1 := e1_2) (e2 := e2_2) as H2.
                    destruct H1 as [H1 | H1];
                    destruct H2 as [H2 | H2];
                    try (right; intros HF; inv HF;
                        contradiction); subst.
                    left. reflexivity.
                - generalize dependent fs0.
                    induction fs; intros gs;
                    destruct gs.
                    + left. reflexivity.
                    + right. intros HF. inv HF.
                    + right. intros HF. inv HF.
                    + destruct (IdDec.eq_dec (fst a) (fst f))
                        as [Hfst | Hfst];
                        destruct (eq_dec (snd a) (snd f)) 
                            as [HAF | HAF];
                        destruct (IHfs gs) as [IH | IH]; subst;
                        try (right; intros HF; inv HF;
                            contradiction).
                        left. inv IH. destruct a.
                        destruct f. simpl in *.
                        subst. reflexivity.
                - destruct (eq_dec e1 e2) as [HE | HE];
                    destruct (IdDec.eq_dec x x0) as [HX | HX];
                    subst; try (right; intros HF;
                        inv HF; contradiction).
                    left. reflexivity.
            Admitted.
            Theorem eq_refl : forall (e : t), e = e.
            Proof. intros. reflexivity. Qed.
            Theorem eq_sym : forall (e1 e2 : t), e1 = e2 -> e2 = e1.
            Proof. unfold eq. intros; subst; reflexivity. Qed.
            Theorem eq_trans : forall (e1 e2 e3 : t), e1 = e2 -> e2 = e3 -> e1 = e3.
            Proof. intros; subst. reflexivity. Qed.
        End ExprDec.

        Module ExprFieldDec := FieldDec(ExprDec).
    End SSExpr.
    Export SSExpr.

    (* Static Semantics with Subsumption *)
    Inductive check (g : gamma) : expr -> type -> Prop :=
        | check_subsume : forall (e : expr) (u v : type),
            subtype u v ->
            check g e u ->
            check g e v
        | check_unit :
            check g EUnit TUnit
        | check_var : forall (x : id) (t : type),
            g x = Some t ->
            check g (EVar x) t
        | check_fun : forall (x : id) (u v : type) (e : expr),
            check (bind x u g) e v ->
            check g (EFun x u e) (TFun u v)
        | check_app : forall (e1 e2 : expr) (u v : type),
            check g e1 (TFun u v) ->
            check g e2 u ->
            check g (EApp e1 e2) v
        | check_rec : forall (es : fields expr) (ts : fields type),
            nodupfs es -> nodupfs ts ->
            relfs (check g) es ts ->
            check g (ERec es) (TRec ts)
        | check_prj : forall (e : expr) (x : id) (t : type) (ts : fields type),
            In (x,t) ts ->
            check g e (TRec ts) ->
            check g (EPrj e x) t.

    Section CheckInduction.
        Variable P : @gamma type -> expr -> type -> Prop.

        Hypothesis HSubsume : 
            forall (g : gamma) (e : expr) (u v : type),
            subtype u v -> check g e u -> P g e u -> P g e v.

        Hypothesis HUnit : 
            forall (g : gamma), P g EUnit TUnit.

        Hypothesis HVar :
            forall (g : gamma) (x : id) (t : type),
            g x = Some t -> 
            P g (EVar x) t.

        Hypothesis HFun :
            forall (g : gamma) (x : id) (u v : type) (e : expr),
            check (bind x u g) e v ->
            P (bind x u g) e v ->
            P g (EFun x u e) (TFun u v).

        Hypothesis HApp :
            forall (g : gamma) (e1 e2 : expr) (u v : type),
            check g e1 (TFun u v) ->
            P g e1 (TFun u v) ->
            check g e2 u ->
            P g e2 u ->
            P g (EApp e1 e2) v.

        Hypothesis HRec :
            forall (g : gamma) (es : fields expr) (ts : fields type),
            nodupfs es -> nodupfs ts ->
            relfs (check g) es ts ->
            relfs (P g) es ts ->
            P g (ERec es) (TRec ts).

        Hypothesis HPrj :
            forall (g : gamma) (e : expr) (x : id) (t : type) (ts : fields type),
            In (x,t) ts ->
            check g e (TRec ts) ->
            P g e (TRec ts) ->
            P g (EPrj e x) t.

        Fixpoint IHCheck (g : gamma) (e : expr) (t : type) (HC :check g e t) : P g e t :=
            match HC in check _ e' t' return (P g e' t') with
            | check_subsume _ e u v HSuv HCeu => 
                HSubsume g e u v HSuv HCeu (IHCheck g e u HCeu)
            | check_unit _ => HUnit g
            | check_var _ x t HB => HVar g x t HB
            | check_fun _ x u v e HCev =>
                HFun g x u v e HCev (IHCheck (bind x u g) e v HCev)
            | check_app _ e1 e2 u v HCe1uv HCe2u =>
                HApp g e1 e2 u v 
                    HCe1uv (IHCheck g e1 (TFun u v) HCe1uv)
                    HCe2u (IHCheck g e2 u HCe2u)
            | check_rec _ es ts NDes NDts HRs =>
                let fix rec_help {es' : fields expr} {ts' : fields type}
                    (HRs' : relfs (check g) es' ts') : Forall2 (relf (P g)) es' ts' :=
                    match HRs' in (Forall2 _ le lt) 
                        return (Forall2 (relf (P g)) le lt) with
                    | Forall2_nil _ => Forall2_nil (relf (P g))
                    | Forall2_cons e t Het Hests =>
                        Forall2_cons
                            e t (relf_pred (IHCheck g) Het) 
                            (rec_help Hests)
                    end in
                HRec g es ts NDes NDts HRs (rec_help HRs)
            | check_prj _ e x t ts Hints HCets =>
                HPrj g e x t ts Hints HCets (IHCheck g e (TRec ts) HCets)
            end.
    End CheckInduction.

    Definition checks : expr -> type -> Prop := check empty.

    Example benjy : 
        checks 
            (EApp 
                (EFun "r" (TRec [("x",TUnit)]) 
                    (EPrj (EVar "r") "x")) 
                (ERec [("x",EUnit);("y",EUnit)]))
            TUnit.
    Proof.
        apply check_app with (u := TRec [("x",TUnit)]).
        - apply check_fun. apply check_prj with 
            (ts := [("x",TUnit)]);
            constructor; reflexivity.
        - apply check_subsume with 
            (u := TRec [("x", TUnit);("y",TUnit)]).
            + apply st_rec_width with
                (us := [("x",TUnit)])
                (vs := [("y",TUnit)]).
            + apply check_rec.
                { constructor; try constructor;
                    try constructor; 
                    try intros DUMB; inv DUMB;
                    try discriminate. inv H. }
                { constructor; try constructor;
                    try constructor; 
                    try intros DUMB; inv DUMB;
                    try discriminate. inv H. }
                { constructor.
                    - split; try reflexivity. constructor. 
                    - constructor.
                        + split.
                            * reflexivity.
                            * constructor.
                        + constructor. }
    Qed. 

    (* Values *)
    Module Value.
        Inductive value : expr -> Prop :=
            | value_unit : value EUnit
            | value_fun : forall (x : id) (t : type) (e : expr),
                value (EFun x t e)
            | value_rec : forall (vs : fields expr),
                predfs value vs ->
                value (ERec vs).

        Section ValueDec.
            Fixpoint value_dec (v : expr) : {value v} + {~ value v}. 
            Proof.
                destruct v.
                - left. constructor.
                - right. intros HF. inv HF.
                - left. constructor.
                - right. intros HF. inv HF.
                - induction fs.
                    + left. constructor. constructor.
                    + destruct (value_dec (snd a)) as [AV | AV].
                        { destruct IHfs as [V | V].
                            - pose proof 
                                (fun x : field expr => value_dec (snd x)) as PFV.
                                pose proof @Forall_dec
                                    (field expr) (predf value) 
                                    PFV fs as FD.
                                destruct FD as [FV | FV].
                                + left. constructor. 
                                    constructor; assumption.
                                + right. intros HF. apply FV.
                                    inv HF. inv H0. assumption.
                            - right. intros HF. apply V. 
                                inv HF. inv H0. constructor.
                                assumption. }
                        { right. intros HF. apply AV. inv HF.
                            inv H0. assumption. }
                - right. intros HF. inv HF.
            Qed.
        End ValueDec.
    End Value.
    Export Value.

    Module Step.
        (* free variables *)
        Fixpoint fv (e : expr) : IS.t :=
            match e with
            | EUnit => IS.empty
            | EVar x => IS.singleton x
            | EFun x _ e => IS.remove x (fv e)
            | EApp e1 e2 => IS.union (fv e1) (fv e2)
            | ERec (es) => 
                fold_right 
                    (fun (e : field expr) acc => 
                        IS.union acc (fv (snd e)))
                    IS.empty es
            | EPrj e _ => fv e
            end.

        (* Capture-avoiding Substitution *)
        Inductive sub (x : id) (es : expr) : expr -> expr -> Prop :=
            | sub_unit : sub x es EUnit EUnit
            | sub_hit : sub x es (EVar x) es
            | sub_miss : forall (y : id), 
                x <> y -> 
                sub x es (EVar y) (EVar y)
            | sub_fun_bound : forall (t : type) (e : expr),
                sub x es (EFun x t e) (EFun x t e)
            | sub_fun_notfree : forall (y : string) (t : type) (e e' : expr),
                x <> y ->
                ~ IS.In y (fv es) -> 
                sub x es e e' -> 
                sub x es (EFun y t e) (EFun y t e')
            | sub_fun_free : forall (y z : id) (t : type) (e e' e'' : expr),
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
            | sub_rec : forall (fs fs' : fields expr),
                relfs (sub x es) fs fs' ->
                sub x es (ERec fs) (ERec fs')
            | sub_prj : forall (e e' : expr) (y : id),
                sub x es e e' ->
                sub x es (EPrj e y) (EPrj e' y).

        Section SubstitutionInduction.
            Variable P : id -> expr -> expr -> expr -> Prop.

            Hypothesis HUnit : 
                forall (x : id) (es : expr), 
                P x es EUnit EUnit.

            Hypothesis HHit : 
                forall (x : id) (es : expr),
                P x es (EVar x) es.

            Hypothesis HMiss : 
                forall (x : id) (es : expr) (y : id),
                x <> y -> P x es (EVar y) (EVar y).

            Hypothesis HFunBound : 
                forall (x : id) (es : expr) (t : type) (e : expr),
                P x es (EFun x t e) (EFun x t e).

            Hypothesis HFunNotFree : 
                forall (x : id) (es : expr) (y : string) (t : type) (e e' : expr),
                x <> y -> ~ IS.In y (fv es) ->
                sub x es e e' -> P x es e e' -> 
                P x es (EFun y t e) (EFun y t e').

            Hypothesis HFunFree :
                forall (x : id) (es : expr) (y z : id)
                (t : type) (e e' e'' : expr),
                x <> y -> x <> z ->
                y <> z -> IS.In y (fv es) ->
                ~ IS.In z (fv es) -> ~ IS.In z (fv e) ->
                sub y (EVar z) e e' -> P y (EVar z) e e' ->
                sub x es e' e'' -> P x es e' e'' -> 
                P x es (EFun y t e) (EFun z t e'').

            Hypothesis HApp :
                forall (x : id) (es e1 e1' e2 e2' : expr),
                sub x es e1 e1' -> P x es e1 e1' ->
                sub x es e2 e2' -> P x es e2 e2' -> 
                P x es (EApp e1 e2) (EApp e1' e2').

            Hypothesis HRec : 
                forall (x : id) (es : expr) (fs fs' : fields expr),
                relfs (sub x es) fs fs' -> 
                relfs (P x es) fs fs' ->
                P x es (ERec fs) (ERec fs').

            Hypothesis HPrj :
                forall (x : id) (es e e' : expr) (y : id),
                sub x es e e' -> P x es e e' -> 
                P x es (EPrj e y) (EPrj e' y).

            Fixpoint IHSubstitute (x : id) (es e e' : expr)
            (HS : sub x es e e') {struct HS} : P x es e e' :=
                match HS in sub _ _ pe pe' return P x es pe pe' with
                | sub_unit _ _ => HUnit x es
                | sub_hit _ _ => HHit x es
                | sub_miss _ _ y Hxy => HMiss x es y Hxy
                | sub_fun_bound _ _ t e => HFunBound x es t e
                | sub_fun_notfree _ _ y t e e' Hxy Hines HS =>
                    HFunNotFree x es y t e e' 
                        Hxy Hines HS (IHSubstitute x es e e' HS)
                | sub_fun_free _ _ y z t e e' e'' 
                    Hxy Hxz Hyz Hinyes Hinzes Hinze HSee' HSe'e'' =>
                    HFunFree x es y z t e e' e'' 
                        Hxy Hxz Hyz Hinyes Hinzes Hinze
                        HSee' (IHSubstitute y (EVar z) e e' HSee')
                        HSe'e'' (IHSubstitute x es e' e'' HSe'e'')
                | sub_app _ _ e1 e1' e2 e2' HS1 HS2 =>
                    HApp x es e1 e1' e2 e2'
                        HS1 (IHSubstitute x es e1 e1' HS1)
                        HS2 (IHSubstitute x es e2 e2' HS2)
                | sub_rec _ _ fs fs' HRs =>
                    let fix rec_help {fds : fields expr} {fds' : fields expr}
                    (HRs' : relfs (sub x es) fds fds') : Forall2 (relf (P x es)) fds fds' :=
                        match HRs' in (Forall2 _ l l') 
                            return (Forall2 (relf (P x es)) l l') with
                        | Forall2_nil _ => Forall2_nil (relf (P x es))
                        | Forall2_cons fd fd' HRhead HRtail =>
                            Forall2_cons
                                fd fd' (relf_pred (IHSubstitute x es) HRhead) 
                                (rec_help HRtail)
                        end in
                    HRec x es fs fs' HRs (rec_help HRs)
                | sub_prj _ _ e e' y HS =>
                    HPrj x es e e' y HS (IHSubstitute x es e e' HS)
                end.
        End SubstitutionInduction.

        Axiom sub_exists : forall (x : id) (s e : expr), exists e', sub x s e e'.

        (* Dynamic Semantics *)
        Inductive step : expr -> expr -> Prop :=
            | step_redux : forall (x : id) (t : type) (e es e' : expr),
                sub x es e e' ->
                step (EApp (EFun x t e) es) e'
            | step_app : forall (e1 e2 e1' : expr),
                step e1 e1' ->
                step (EApp e1 e2) (EApp e1' e2)
            | step_prj_rec : forall (es : fields expr) (x : id) (e : expr),
                In (x,e) es ->
                step (EPrj (ERec es) x) e
            | step_prj : forall (e e' : expr) (x : id),
                step e e' ->
                step (EPrj e x) (EPrj e' x)
            | step_rec : forall (vs es : fields expr) (x : id) (e e' : expr),
                predfs value vs ->
                step e e' ->
                step (ERec (vs ++ (x,e) :: es)) (ERec (vs ++ (x,e') :: es)).
    End Step.
    Export Step.

    (* Inversion on Subsumption. *)
    Section InvSubsumption.
        Lemma inv_top :
            forall (t : type),
            subtype TTop t -> t = TTop.
        Proof.
            intros t HS. dependent induction HS; auto.
        Qed.

        Lemma inv_empty_rec_subtype :
            forall (t : type),
            subtype (TRec []) t ->
            t = TTop \/ t = (TRec []).
        Proof.
            intros t HS;
            dependent induction HS using IHSubtype;
            try (left; reflexivity);
            try (right; reflexivity).
            - assert (HRe : TRec [] = TRec []);
                try reflexivity.
                apply IHHS1 in HRe as IH1.
                destruct IH1 as [IH1 | IH1]; subst.
                + apply inv_top in HS2. subst.
                    left. reflexivity.
                + apply IHHS2 in HRe as IH2.
                    destruct IH2 as [IH2 | IH2]; subst.
                    * left. reflexivity.
                    * right. reflexivity.
            - apply app_eq_nil in x as [Hus Hvs].
                subst. right. reflexivity.
            - inv H0. right. reflexivity.
            - apply Permutation_nil in H.
                subst. right. reflexivity.
        Qed.

        Lemma subtype_empty_rec :
            forall (ss : fields type),
            subtype (TRec ss) (TRec []).
        Proof.
            intros ss. assert (H : ss = [] ++ ss); 
            try reflexivity. rewrite H. constructor.
        Qed.

        Lemma inv_unit :
            forall (t : type),
            subtype t TUnit -> t = TUnit.
        Proof.
            intros t HS. dependent induction HS; auto.
        Qed.

        Lemma inv_fun :
            forall (t a b : type),
            subtype t (TFun a b) ->
            exists (a' b' : type),
            t = TFun a' b' /\ subtype a a' /\ subtype b' b.
        Proof.
            intros t a b HS.
            dependent induction HS.
            - exists a. exists b. split.
                + reflexivity.
                + split; constructor.
            - specialize IHHS2 with 
                (a0 := a) (b0 := b).
                assert (HR : TFun a b = TFun a b);
                try reflexivity.
                apply IHHS2 in HR as [a' [b' [HU [HSA HSB]]]].
                apply IHHS1 in HU as [a'' [b'' [HT [HSA' HSB']]]].
                exists a''. exists b''. split.
                + assumption.
                + split.
                    * apply st_trans with
                        (t := a) (u := a') (v := a'');
                        assumption.
                    * apply st_trans with
                        (t := b'') (u := b') (v := b);
                    assumption.
            - exists u. exists v. split.
                + reflexivity.
                + split; assumption.
        Qed.

        Lemma inv_rec :
            forall (t : type) (ts : fields type),
            subtype t (TRec ts) ->
            exists (us : fields type),
            t = TRec us /\ subtype (TRec us) (TRec ts).
        Proof.
            intros t ts HS. dependent induction HS.
            - exists ts. split; auto.
                apply st_refl.
            - specialize IHHS2 with (ts0 := ts).
                assert (HRts : TRec ts = TRec ts);
                try reflexivity.
                apply IHHS2 in HRts as IH2.
                destruct IH2 as [us [HU HSusts]].
                specialize IHHS1 with (ts := us).
                apply IHHS1 in HU as IH1.
                destruct IH1 as [vs [HT HSvsus]].
                exists vs. split; auto.
                apply st_trans with 
                    (t := (TRec vs)) (u := TRec us) (v := TRec ts);
                assumption.
            - exists (ts ++ vs). split; constructor.
            - exists us. split; constructor. assumption.
            - exists us. split; auto.
                apply st_rec_perm. assumption.
        Qed.

        Lemma subtype_cons_rec :
            forall (t : field type) (ss ts : fields type),
            subtype (TRec ss) (TRec (t :: ts)) ->
            exists s' ss', ss = s' :: ss'.
        Proof.
            intros t ss ts HS.
            dependent induction HS using IHSubtype.
            - exists t. exists ts. reflexivity.
            - apply inv_rec in HS2
                as [us [Huus Hustts]]; subst.
                assert (Hssss : TRec ss = TRec ss);
                assert (Husus : TRec us = TRec us);
                try reflexivity.
                apply IHHS2 with (t0 := t) (ts0 := ts) in Husus as IH2; 
                try reflexivity; clear IHHS2.
                destruct IH2 as [s' [ss' Huss'ss']]. subst.
                apply IHHS1  with (t := s') (ts := ss') 
                    in Hssss as IH1; try reflexivity; clear IHHS1.
                apply IH1.
            - exists t. exists (ts ++ vs).
                rewrite app_comm_cons.
                reflexivity.
            - destruct ss.
                + inv H0.
                + exists f. exists ss.
                    reflexivity.
            - destruct ss.
                + apply Permutation_nil_cons in H. contradiction.
                + exists f. exists ss. reflexivity.
        Qed.

        Lemma cons_rec_same :
            forall (ss ts : fields type),
            subtype (TRec ss) (TRec ts) ->
            forall (u : field type),
            subtype (TRec (u :: ss)) (TRec (u :: ts)).
        Proof.
            intros ss ts HS.
            dependent induction HS
                using IHSubtype; intros v.
            - constructor.
            - apply inv_rec in HS2.
                destruct HS2 as [us [Huus HSusts]]. subst. 
                assert (HEus : TRec us = TRec us);
                assert (HEss : TRec ss = TRec ss);
                assert (HEts : TRec ts = TRec ts);
                try reflexivity.
                apply IHHS1 with (ts := us) (u := v) 
                    in HEss as IH2; auto.
                apply IHHS2 with (ts0 := ts) (u := v)
                    in HEus as IH1; auto.
                    apply st_trans with (u := TRec (v :: us)); auto.
            - rewrite app_comm_cons.
                apply st_rec_width.
            - constructor. induction H0.
                + apply st_fields_refl.
                + constructor; auto.
                    split; auto.
                    constructor.
            - apply st_rec_perm.
                apply perm_skip; auto.
        Qed.

        Lemma cons_subtype_rec :
            forall (ss ts : fields type),
            subtype (TRec ss) (TRec ts) ->
            forall (s t : field type),
            relf subtype s t ->
            subtype (TRec (s :: ss)) (TRec (t :: ts)).
        Proof.
            intros ss ts HS.
            dependent induction HS using IHSubtype;
            intros s t HRst.
            - apply st_rec_depth.
                constructor; auto.
                apply st_fields_refl.
            - apply inv_rec in HS2.
                destruct HS2 as [us [Huus HSusts]]. subst. 
                assert (HEus : TRec us = TRec us);
                assert (HEss : TRec ss = TRec ss);
                assert (HEts : TRec ts = TRec ts);
                try reflexivity.
                apply IHHS1 with (ts := us) (s := s) (t := s) 
                    in HEss as IH1; auto; clear IHHS1.
                apply IHHS2 with (ts0 := ts) (s := s) (t := t)
                    in HEus as IH2; auto; clear IHHS2.
                apply st_trans with (u := TRec (s :: us)); auto.
                constructor; auto. constructor.
            - rewrite app_comm_cons.
                apply st_trans with (u := (TRec (s :: ts)));
                constructor. constructor; auto.
                apply st_fields_refl.
            - apply st_rec_depth. constructor; auto.
            - apply st_trans with (u := TRec (s :: ts)).
                + apply cons_rec_same.
                    apply st_rec_perm. assumption.
                + constructor. constructor; auto.
                    apply st_fields_refl.
        Qed.

        Lemma rec_subtype_depth_trans_1 :
            forall (ss ts : fields type),
            subtype (TRec ss) (TRec ts) <->
            exists us, relfs subtype us ts /\
            subtype (TRec ss) (TRec us).
        Proof.
            intros ss ts. split.
            - intros H. exists ts. split; auto.
                apply st_fields_refl.
            - intros [us [HRusts HSssus]].
                apply st_trans with (u := TRec us); auto.
                apply st_rec_depth. assumption.
        Qed.

        (* I think this is true, but
            I give up on proving it... :( *)
        Lemma rec_subtype_equiv :
            forall (ss ts : fields type),
            (forall t, In t ts ->
            exists s, In s ss /\ relf subtype s t) ->
            exists (us vs : fields type),
            perm ss (us ++ vs) /\ relfs subtype us ts.
        Proof.
            intros ss ts. generalize dependent ss.
            induction ts; intros ss H.
            - exists []. exists ss.
                simpl. split.
                + apply Permutation_refl.
                + apply st_fields_refl.
            - assert (Hinaats : In a (a :: ts));
                try apply in_eq.
                apply H in Hinaats as [s [Hinsss HRsa]]; clear H.
                destruct ss.
                + inv Hinsss.
                + destruct (TypeFieldDec.eq_dec s f); subst.
                    * admit.
                    * inv Hinsss; try contradiction.
        Admitted.

        Lemma alt_rec_subtyping :
            forall (ss ts : fields type),
            (forall t, In t ts ->
            exists s, In s ss /\ relf subtype s t) ->
            subtype (TRec ss) (TRec ts).
        Proof. 
            intros ss ts H.
            assert (HUV : exists (us vs : fields type),
            perm ss (us ++ vs) /\ relfs subtype us ts).
            - apply rec_subtype_equiv. assumption. 
            - destruct HUV as [us [vs [HRusts HPss]]].
                apply st_trans with (u := TRec (us ++ vs)).
                try (apply st_rec_perm; assumption).
                apply st_trans with (u := TRec us);
                try apply st_rec_width.
                apply st_rec_depth. assumption.
        Qed.
    End InvSubsumption.

    Section CanonicalForms.
        Definition canon_unit (v : expr) : Prop :=
            value v -> checks v TUnit -> v = EUnit.

        Definition canon_fun (v : expr) : Prop :=
            forall (a b : type),
            value v -> checks v (TFun a b) -> 
            exists (x : id) (t : type) (e : expr), 
            subtype a t /\ v = EFun x t e.

        Definition canon_rec (v : expr) := 
            forall (ts : fields type),
            value v -> checks v (TRec ts) ->
            exists (es : fields expr) (us : fields type), 
            v = ERec es /\
            relfs (check empty) es us /\ 
            subtype (TRec us) (TRec ts).

        Lemma canonical_forms_unit : 
            forall (v : expr), canon_unit v.
        Proof.
            unfold canon_unit. intros v HV HChk;
            dependent induction HChk.
            - apply inv_unit in H as HU. auto.
            - reflexivity.
            - inversion HV.
            - inversion HV.
            - inversion HV.
        Qed.

        Lemma canonical_forms_fun :
            forall (v : expr), canon_fun v.
        Proof.
            unfold canon_fun. intros v t t' HV HChk.
            dependent induction HChk.
            - apply inv_fun in H as HU.
                destruct HU as [a' [b' [HF [HSA HSB]]]].
                specialize IHHChk with
                    (t := a') (t' := b').
                pose proof (IHHChk HV HF) as IH.
                destruct IH as [x [w [e' [HSW HFW]]]].
                exists x. exists w. exists e'. split.
                + apply st_trans with
                    (t := t) (u := a') (v := w);
                    assumption.
                + assumption.
            - inversion HV.
            - exists x. exists t. exists e. 
                split; constructor.
            - inversion HV.
            - inversion HV.
        Qed.

        Lemma canonical_forms_rec :
            forall (v : expr), canon_rec v.
        Proof.
            unfold canon_rec. intros v ts HV HChk.
            dependent induction HChk.
            - apply inv_rec in H as [us [HU HSusts]].
                specialize IHHChk with (ts := us).
                apply IHHChk in HV as IH; auto.
                destruct IH as [es [vs [Hrec [HR HSvsus]]]].
                exists es. exists vs. split; auto. split; auto.
                apply st_trans with
                    (t := (TRec vs)) (u := (TRec us)) (v := (TRec ts));
                assumption.
            - inv HV.
            - inv HV.
            - exists es. exists ts. 
                split; try reflexivity.
                induction HV; subst; constructor;
                try assumption;
                try apply st_refl.
            - inv HV. 
        Qed.
    End CanonicalForms.

    Section Progress.
        Lemma st_fields_name :
            forall (us ws : fields type),
            subtype (TRec us) (TRec ws) ->
            forall (x : id) (w : type),
            In (x,w) ws ->
            exists (u : type),
            In (x,u) us /\ subtype u w.
        Proof.
            intros us ws HS.
            dependent induction HS using IHSubtype; intros x w Hinws.
            - subst. exists w. 
                split; auto. constructor.
            - assert (HSusws : subtype (TRec us) (TRec ws)).
                + apply st_trans with (u := u); assumption.
                + pose proof inv_rec u ws HS2 as [vs [Huvs HSvws]]. subst.
                    assert (Hduhu : TRec us = TRec us);
                    assert (Hduhv : TRec vs = TRec vs);
                    assert (Hduhw : TRec ws = TRec ws);
                    try reflexivity.
                    pose proof IHHS2 vs ws Hduhv Hduhw x w as IH2.
                    apply IH2 in Hinws as [w' [Hinvs HSw'w]].
                    pose proof IHHS1 us vs Hduhu Hduhv x w' as IH1.
                    apply IH1 in Hinvs as [u' [Hinus Hsubu'w']].
                    exists u'. split; try assumption.
                    apply st_trans with (u := w');
                    assumption.
            - exists w. split.
                + apply in_or_app.
                    left. auto.
                + constructor.
            - induction H0; inv Hinws.
                + inv H. inv H5. destruct x0 as [x0 u0].
                    exists u0. split.
                    * constructor. simpl in H2.
                        rewrite <- H2. reflexivity.
                    * assumption.
                + inv H. pose proof IHForall2 H8 H2 as HEX.
                    destruct HEX as [u [Hinl HSuw]].
                    exists u. split; try assumption.
                    apply in_cons. assumption.
            - exists w. apply Permutation_sym in H. split.
                + apply Permutation_in with (l := ws);
                    assumption.
                + constructor.
        Qed.

        Lemma rec_fields_name :
            forall (es : fields expr) (ts : fields type),
            relfs checks es ts ->
            forall (x : id) (t : type),
            In (x,t) ts ->
            exists (e : expr), In (x,e) es.
        Proof.
            intros es ts HR. induction HR;
            intros z t Hints.
            - inv Hints.
            - destruct x as (x,e). inv Hints.
                + exists e. constructor.
                    unfold relf in H.
                    destruct H as [HF _].
                    simpl in *. subst.
                    reflexivity.
                + apply IHHR in H0 as [e' Hinl].
                    exists e'. apply in_cons.
                    assumption.
        Qed.

        Definition progress_thm (e : expr) (t : type) : Prop :=
            checks e t -> value e \/ exists (e' : expr), step e e'.

        Lemma var_empty_checks :
            forall (x : id) (t : type),
            ~ checks (EVar x) t.
        Proof.
            intros x t H. unfold checks in *.
            remember empty as o in H. 
            remember (EVar x) as z in H.
            dependent induction H; 
            auto; try inv Heqz.
            discriminate.
        Qed.

        Lemma val_rec_exists :
            forall (es : fields expr),
            ~ value (ERec es) <-> Exists (predf (fun e => ~ value e)) es.
        Proof.
            intros es. split; intros H.
            - induction es.
                + exfalso. apply H.
                    constructor. constructor.
                + apply Exists_cons. 
                    destruct (value_dec (snd a)).
                    * right. apply IHes. intros V.
                        inv V. apply H. constructor.
                        constructor; assumption.
                    * left. unfold predf. assumption.
            - intros V. apply Exists_Forall_neg in H.
                + apply H. inv V. assumption.
                + pose proof 
                    (fun x : field expr => 
                        value_dec (snd x)) as PFV.
                    intros e. specialize PFV with e.
                    destruct PFV as [VE | VE]; auto.
        Qed.

        Lemma val_rec_prefix :
            forall (es : fields expr),
            ~ value (ERec es) ->
            exists (x : id) (e : expr) 
                (qs rs : fields expr),
            ~ value e /\ 
            predfs value qs /\
            es = qs ++ (x,e) :: rs.
        Proof.
            induction es; intros HV.
            - exfalso. apply HV.
                constructor. constructor.
            - destruct (value_dec (snd a)).
                { assert (HVes : ~ value (ERec es)).
                    - intros HR. apply HV. inv HR.
                        constructor.
                        constructor; assumption.
                    - pose proof IHes HVes as IH.
                        destruct IH as [x [e [qs [rs [HNV [HPV Hqer]]]]]].
                        exists x. exists e. exists (a :: qs). 
                        exists rs. split; try assumption. split.
                        + constructor; assumption.
                        + rewrite <- app_comm_cons.
                            rewrite Hqer. reflexivity. }
                { exists (fst a). exists (snd a).
                    exists []. exists es. split;
                    try assumption. split.
                    - constructor.
                    - rewrite app_nil_l. destruct a as (x,e).
                        reflexivity. }
        Qed.

        Theorem Progress :
            forall (e : expr) (t : type), progress_thm e t.
        Proof.
            unfold progress_thm. intros e t HC.
            unfold checks in *. remember empty as o in HC.
            dependent induction HC using IHCheck; subst;
            assert (HE : @empty type = @empty type);
            try reflexivity.
            - destruct IHHC as [V | [e' HS]].
                + reflexivity.
                + left. assumption.
                + right. exists e'. assumption.
            - left. constructor.
            - discriminate.
            - left. constructor.
            - right. pose proof IHHC1 HE as [V | [e1' HS]].
                + pose proof canonical_forms_fun e1 u v V HC1
                    as [x [t [e [HS HF]]]].
                    pose proof sub_exists x e2 e as [e' HSub].
                    exists e'. subst. constructor. assumption.
                + exists (EApp e1' e2). constructor. assumption.
            - induction H2.
                + left. constructor. constructor.
                + inv H. inv H1. inv H0. clear H. clear H0. inv H2.
                    pose proof IHForall2 H7 as IH2.
                    destruct H2 as [HFXY YES].
                    pose proof YES HE as [HVX | [e' HSX]].
                    { destruct (value_dec (ERec l)) as [V | V].
                        - left. constructor. inv V.
                            constructor; auto.
                        - destruct IH2 as [IH2 | IH2]; try contradiction; auto. 
                            pose proof val_rec_prefix l V as HEX.
                            destruct HEX as [z [e [qs [rs [HVE [HPV HL]]]]]].
                            right. subst. destruct IH2 as [e' HS]. inv HS.
                            exists (ERec (x :: vs ++ (x0,e'0) :: es)).
                            rewrite app_comm_cons. rewrite app_comm_cons.
                            constructor; auto.
                            constructor; auto. }
                    { right. destruct x as [x e]. simpl in *.
                        exists (ERec ((x, e') :: l)).
                        assert (HPV : predfs value []);
                        try (constructor; constructor).
                        pose proof step_rec [] l x e e' HPV HSX as HR.
                        rewrite app_nil_l in HR. rewrite app_nil_l in HR.
                        assumption. }
            - right. pose proof IHHC HE as [V | [e' HS]].
                + pose proof canonical_forms_rec e ts V HC as HCF.
                    destruct HCF as [es [us [HRec [HR Hsub]]]]; subst.
                    pose proof st_fields_name us ts Hsub x t H as [u [Hinus HSut]].
                    pose proof rec_fields_name es us HR x u Hinus as [e' Hines].
                    exists e'. constructor. assumption.
                + exists (EPrj e' x). constructor. assumption.
        Qed.
    End Progress.

    (* Inversion on the Typing Relation. *)
    Section InvCheck.
        Lemma inv_chk_fun :
            forall (g : gamma) (t u v : type) (x : id) (e : expr),
            check g (EFun x t e) (TFun u v) ->
            subtype u t /\ check (bind x t g) e v.
        Proof.
            intros g t u v x e HC. 
            dependent induction HC using IHCheck.
            - pose proof inv_fun u0 u v H as [a [b [Huab [Hua Hbv]]]].
                subst. assert (HEFun : EFun x t e = EFun x t e);
                assert (HTFun : TFun a b = TFun a b); try reflexivity.
                pose proof IHHC t a b x e HEFun HTFun as IH.
                destruct IH as [HS HCB]. split.
                + apply st_trans with (u := a); assumption.
                + apply check_subsume with (u := b); assumption.
            - split; try apply st_refl. assumption.
        Qed.

        Lemma inv_chk_rec :
            forall (g : gamma) (es : fields expr) (ts : fields type),
            check g (ERec es) (TRec ts) ->
            forall (x : id) (t : type),
            In (x,t) ts ->
            exists (e : expr), 
            In (x,e) es /\ check g e t.
        Proof.
            intros g es ts HC x t Hints.
            dependent induction HC using IHCheck.
            - pose proof inv_rec u ts H as HRu.
                destruct HRu as [us [Huus HSus]].
                assert (HERec : ERec es = ERec es);
                try reflexivity.
                pose proof st_fields_name us ts HSus x t Hints as HT.
                destruct HT as [w [Hinus HSut]].
                pose proof IHHC es us HERec Huus x w Hinus as IH.
                destruct IH as [e [Hines HCew]]. exists e. split.
                + assumption.
                + apply check_subsume with (u := w);
                    assumption.
            - induction H2; inv Hints;
                inv H; inv H0; clear H; clear H0;
                inv H1; clear H1.
                + destruct x0 as [x0 e0]. exists e0. 
                    destruct H5 as [Hfst Hck].
                    simpl in *; subst. split.
                    * left. reflexivity.
                    * assumption.
                + pose proof IHForall2 H8 H10 H12 H4 as IH. 
                    destruct IH as [e [HIN HCK]].
                    exists e. split; try assumption.
                    apply in_cons. assumption.
        Qed.

        Lemma inv_chk_rec' :
            forall (g : gamma) (es : fields expr) (ts : fields type),
            check g (ERec es) (TRec ts) ->
            forall (x : id) (t : type),
            In (x,t) ts ->
            forall (e : expr),
            In (x,e) es ->
            check g e t.
        Proof.
            intros g es ts HC x t Hints.
            intros f Hinfes.
            dependent induction HC using IHCheck.
            - apply inv_rec in H as [us [Huus HSusts]].
                pose proof st_fields_name 
                    us ts HSusts x t Hints as SFN.
                destruct SFN as [w [Hinus HSwt]].
                apply check_subsume with (u := w); auto.
                apply IHHC with (es0 := es) (ts := us) (x := x);
                auto. 
            - assert (HC : check g (ERec es) (TRec ts)).
                + constructor; auto.
                + pose proof inv_chk_rec g es ts 
                    HC x t Hints as ICR.
                    destruct ICR as [e [Hin Hget]].
                    pose proof relfs_nodup_eq es x e f 
                        H Hin Hinfes as EF. subst.
                        assumption.                  
        Qed.
    End InvCheck.

    Section SubstitutionLemma.
        Lemma bind_unfree_var :
            forall (e : expr) (x : id) (u v : type) (g : gamma),
            ~ IS.In x (fv e) ->
            check g e u <-> check (bind x v g) e u.
        Proof.
            intros e x u v g HN. split; intros HC;
            dependent induction HC using IHCheck.
            - pose proof IHHC HN as IH.
                apply check_subsume with (u := u);
                assumption.
            - constructor.
            - constructor. simpl in *.
                assert (Hxx0 : x <> x0).
                + intros Hxx0. apply HN. subst.
                    constructor. reflexivity.
                + apply bind_complete; assumption.
            - constructor. destruct (IdDec.eq_dec x x0) as [HX | HX]; subst.
                + rewrite <- rebind_correct. assumption.
                + simpl in *. assert (HNin : ~ IS.In x (fv e)).
                    * intros HNin. apply HN.
                        apply not_eq_sym in HX.
                        apply ISF.remove_2; assumption.
                    * pose proof bind_diff_comm x x0 v u g HX as BDC.
                        rewrite <- BDC. pose proof IHHC HNin as IH.
                        assumption.
            - simpl in *. apply check_app with (u := u).
                + apply IHHC1. intros H1. apply HN.
                    apply ISF.union_2. assumption.
                + apply IHHC2. intros H2. apply HN.
                    apply ISF.union_3. assumption.
            - constructor; auto. clear H. clear H0.
                induction H2;
                constructor; inv H1; inv H.
                + split; try assumption. apply H3.
                    intros Hxx0. apply HN. simpl.
                    apply ISF.union_3. assumption.
                + assert (Hxl : ~ IS.In x (fv (ERec l))).
                    * intros Hxl. apply HN. simpl in *.
                        apply ISF.union_2. assumption.
                    * apply (IHForall2 Hxl H7).
            - simpl in *. apply check_prj with (ts := ts);
                try assumption. auto.
            - pose proof IHHC x v g HN as IH.
                apply check_subsume with (u := u); auto.
            - constructor.
            - simpl in *. constructor.
                assert (Hxx0 : x <> x0).
                + intros Hxx0. apply HN. subst.
                    constructor. reflexivity.
                + apply bind_complete in H; assumption.
            - constructor. destruct (IdDec.eq_dec x x0) as [HX | HX]; subst.
                + rewrite <- rebind_correct in HC. assumption.
                + simpl in *. assert (HNin : ~ IS.In x (fv e)).
                    * intros HNin. apply HN.
                        apply not_eq_sym in HX.
                        apply ISF.remove_2; assumption.
                    * pose proof bind_diff_comm x x0 v u g HX as BDC.
                        symmetry in BDC.
                        pose proof IHHC x v (bind x0 u g) HNin BDC as IH.
                        apply IH.
            - simpl in *. apply check_app with (u := u).
                + apply IHHC1 with (x0 := x) (v1 := v); 
                    auto. intros H1. apply HN. 
                    apply ISF.union_2. assumption.
                + apply IHHC2 with (x0 := x) (v0 := v); 
                    auto. intros H2. apply HN. 
                    apply ISF.union_3. assumption.
            - constructor; auto. induction H2; 
                constructor; inv H; inv H0;
                clear H; clear H0; inv H1; inv H2; inv H5.
                + split; try assumption.
                    apply H0 with (x1 := x) (v0 := v); auto.
                    intros Hxx0. apply HN. simpl.
                    apply ISF.union_3. assumption.
                + assert (Hxl : ~ IS.In x (fv (ERec l))).
                    * intros Hxl. apply HN. simpl in *.
                        apply ISF.union_2. assumption.
                    * apply (IHForall2 H7 H9 H11 Hxl).
            - apply check_prj with (ts := ts); auto.
                simpl in *. assert (HR : bind x v g = bind x v g);
                try reflexivity. pose proof IHHC x v g HN HR as IH.
                assumption.
        Qed.

        Definition substitution_lemma (x : id) (esub e e' : expr) :=
            sub x esub e e' ->
            forall (u v : type) (g : gamma),
            check (bind x u g) e v -> 
            check g esub u -> 
            check g e' v.

        Lemma fields_sub_nodups :
            forall (x : id) (esub : expr) (es es' : fields expr),
            relfs (sub x esub) es es' ->
            nodupfs es -> nodupfs es'.
        Proof.
            intros x esub es es' HS.
            induction HS; intros ND.
            - constructor.
            - destruct x0 as [x0 ex0].
                destruct y as [y ey].
                destruct H as [Hfst Hsub].
                simpl in *. subst.
                inv ND.
                unfold nodupfs in *. simpl in *.
                constructor; simpl in *; auto.
                intros Hin. apply H1.
                pose proof relfs_name_share (sub x esub) as RNS.
                apply RNS with (x0 := y) in HS. 
                apply HS. assumption.
        Qed.

        Lemma SubstitutionLem :
            forall (x : id) (esub e e' : expr),
            substitution_lemma x esub e e'.
        Proof.
            intros x esub e e' HS.
            induction HS using IHSubstitute;
            intros u v g HCB;
            remember g as g' in HCB; 
            dependent induction HCB; intros HC;
            try (apply check_subsume with (u := u0); auto;
                apply IHHCB with (x0 := x) (u1 := u) (g' := g); 
                try reflexivity; assumption);
            assert (Hgg : g = g); try reflexivity.
            - constructor.
            - rewrite bind_correct in H. injintrosubst H. auto.
            - apply bind_complete in H0 as BC; auto.
                constructor. auto.
            - constructor. clear IHHCB. 
                rewrite <- rebind_correct in HCB.
                assumption.
            - pose proof IHHCB g Hgg u e t y 
                H0 x H HS IHHS as IH.
                apply check_subsume with (u := u0); auto.
            - clear IHHCB. constructor.
                rewrite <- (bind_diff_comm x y u t g H) in HCB.
                apply IHHS in HCB as IH; auto.
                apply bind_unfree_var; auto.
            - pose proof IHHCB g Hgg u H3 e H4 t y 
                H1 H2 HS1 IHHS1 x H H0 HS2 IHHS2 as IH.
                apply check_subsume with (u := u0); auto.
            - clear IHHCB. constructor.
                apply IHHS2 with (u := u).
                { apply IHHS1 with (u := t).
                    - pose proof bind_diff_comm 
                        x z u t g H0 as BDC1.
                        rewrite BDC1.
                        pose proof bind_diff_comm
                            y z t t (bind x u g) H1 as BDC2.
                        rewrite BDC2. apply bind_unfree_var; auto.
                    - apply bind_unfree_var.
                        + intros Hin. simpl in *.
                            apply IS.singleton_spec in Hin.
                            contradiction.
                        + constructor. apply bind_correct. }
                { apply bind_unfree_var; auto. }
            - pose proof IHHCB x e1 e2 HS1 HS2
                IHHS1 IHHS2 u g as IH.
                apply check_subsume with (u := u0); auto.
            - clear IHHCB1. clear IHHCB2.
                apply check_app with (u := u0).
                + apply IHHS1 with (u := u); auto.
                + apply IHHS2 with (u := u); auto.
            - pose proof IHHCB x fs H H0 u g as IH.
                apply check_subsume with (u := u0); auto. 
            - apply check_rec; auto.
                + apply fields_sub_nodups in H; auto.
                + generalize dependent fs'.
                induction H1; intros fs';
                intros HSfs; intros Hbig;
                inv HSfs; constructor; auto;
                destruct x0 as [x0 ex0];
                destruct y as [y ey];
                destruct y0 as [y0 ey0];
                destruct H5 as [Hfst Hsub];
                inv HSfs; clear HSfs;
                inv Hbig; clear Hbig;
                destruct H8 as [Hfst' Hck];
                destruct H as [Hyy0 Hcky];
                simpl in *; subst; clear Hfst'.
                * split; auto; simpl. 
                    apply Hck with (u := u); auto.
                * inv H2; clear H2.
                    inv H3; clear H3. clear H4. clear H2.
                    pose proof IHForall2 H5 H8
                        l'0 H9 H11 as IH; clear IHForall2.
                    apply IH.
            - pose proof IHHCB x e y HS  IHHS u g as IH.
                apply check_subsume with (u := u0); auto.
            - clear IHHCB. apply check_prj with (ts := ts); auto.
                apply IHHS in HCB as IH; auto.
        Qed.
    End SubstitutionLemma.

    Section Preservation.
        Definition preservation (e e' : expr) : Prop :=
            step e e' -> forall (t : type),
            checks e t -> checks e' t.

        Theorem Preservation :
            forall (e e' : expr), preservation e e'.
        Proof.
            intros e e' HS.
            dependent induction HS; intros u HC;
            unfold checks in *;
            remember empty as o in HC.
            - dependent induction HC.
                + apply check_subsume with (u := u); auto.
                    apply IHHC with (x0 := x) (t0 := t)
                    (e0 := e) (es0 := es); auto.
                + clear IHHC1. clear IHHC2.
                    apply inv_chk_fun in HC1 as [HSut Hev].
                    apply SubstitutionLem in H as SL.
                    apply SL with (u := t); auto.
                    apply check_subsume with (u := u); auto.
            - dependent induction HC.
                + apply check_subsume with (u := u); auto.
                    apply IHHC with (e3 := e1) (e4 := e2); auto.
                + clear IHHC1. clear IHHC2.
                    apply check_app with (u := u); auto.
            - generalize dependent e.
                dependent induction HC;
                intros e Hin.
                + apply check_subsume with (u := u); auto.
                    apply IHHC with (es0 := es) (x0 := x); auto.
                + clear IHHC.
                    pose proof inv_chk_rec' empty 
                        es ts HC x t H e Hin as ICR.
                    assumption.
            - dependent induction HC.
                + apply check_subsume with (u := u); auto.
                    apply IHHC with (e0 := e) (x0 := x); auto.
                + clear IHHC. apply check_prj with (ts := ts); auto.
            - dependent induction HC.
                { apply check_subsume with (u := u); auto.
                    apply IHHC with (e0 := e) 
                        (x0 := x) (es0 := es) (vs0 := vs); auto. }
                { constructor; auto.
                    - unfold nodupfs in *.
                        rewrite map_app.
                        rewrite map_app in H2.
                        simpl in *. assumption.
                    - apply relfs_app in H1 as RA.
                        destruct RA as [ts1 [ts2 [Hts [Hts1 Hts2]]]].
                        subst. inv Hts2.
                        inv H5. apply IHHS in H4.
                        apply relfs_app_dist; auto.
                        constructor; auto.
                        constructor; auto. }
        Qed.
    End Preservation.
End SubsumptionSTLC.

Module Coercion.
    Module SS := SubsumptionSTLC.
    Module SST := SS.SSType.
    Module SSE := SS.SSExpr.

    Inductive type : Type :=
        | TUnit
        | TFun (t t' : type)
        | TRec (ts : fields type).

    Inductive expr : Type :=
        | EUnit
        | EVar (x : id)
        | EFun (x : id) (t : type) (e : expr)
        | EApp (e1 e2 : expr)
        | ERec (es : fields expr)
        | EPrj (e : expr) (x : id).

    (* free variables *)
    Fixpoint fv (e : expr) : IS.t :=
        match e with
        | EUnit => IS.empty
        | EVar x => IS.singleton x
        | EFun x _ e => IS.remove x (fv e)
        | EApp e1 e2 => IS.union (fv e1) (fv e2)
        | ERec (es) => 
            fold_right 
                (fun (e : field expr) acc => 
                    IS.union acc (fv (snd e)))
                IS.empty es
        | EPrj e _ => fv e
        end.

    Inductive check (g : @gamma type) : expr -> type -> Prop :=
        | check_unit : check g EUnit TUnit
        | check_var : forall (x : id) (t : type),
            g x = Some t ->
            check g (EVar x) t
        | check_fun : forall (x : id) (t t' : type) (e : expr),
            check (bind x t g) e t' ->
            check g (EFun x t e) (TFun t t')
        | check_app : forall (e1 e2 : expr) (t t' : type),
            check g e1 (TFun t t') ->
            check g e2 t ->
            check g (EApp e1 e2) t'
        | check_rec : forall (es : fields expr) (ts : fields type),
            relfs (check g) es ts ->
            check g (ERec es) (TRec ts)
        | check_prj : forall (e : expr) (x : id) (t : type) (ts : fields type),
            In (x,t) ts ->
            check g e (TRec ts) ->
            check g (EPrj e x) t.

    Fixpoint translate_type (t : SST.type) : type :=
        match t with
        | SST.TTop | SST.TUnit => TUnit
        | SST.TFun t t' => 
            TFun (translate_type t) (translate_type t')
        | SST.TRec ts =>
            TRec (map (map_snd translate_type) ts)
        end.

    (* Why Coq:
        Incorrect elimination of "HS'" in the inductive type "Forall2":
        the return type has sort "Type" while it should be "Prop".
        Elimination of an inductive object of sort Prop
        is not allowed on a predicate in sort Type
        because proofs can be eliminated only to build proofs. *)
    Fail Fixpoint rechelp {ss' ts' : fields SST.type} 
    (HS' : relfs SS.subtype ss' ts') : fields expr :=
        match HS' with
        | Forall2_nil _ => []
        | Forall2_cons s _ (conj _ Hst) Hssts =>
            (fst s, EUnit) :: (rechelp Hssts)
        end.

    (* why Coq, why? I cannot define the translation
        as a function from subtyping derivations 
        to types... :( *)
    Fail Fixpoint translate_subtype {u v : SST.type} (HS : SS.subtype u v) : expr :=
        let x := EVar "x" in
        let f := EVar "f" in
        let r := EVar "r" in
        match HS with
        | SS.st_refl t => EFun "x" (translate_type t) x
        | SS.st_trans s _ _ HSsu HSut => 
            EFun "x" (translate_type s) 
                (EApp (translate_subtype HSsu)
                    (EApp (translate_subtype HSut) x))
        | SS.st_top t => EFun "x" (translate_type t) EUnit
        | SS.st_fun s1 s2 t1 _ C1 C2 =>
            EFun "f" (translate_type (SST.TFun s1 s2 ))
                (EFun "x" (translate_type t1) 
                    (EApp (translate_subtype C2) 
                        (EApp f
                            (EApp (translate_subtype C1) x))))
        | SS.st_rec_width us vs =>
            EFun "r" 
                (TRec (map (map_snd translate_type) (us ++ vs)))
                (ERec 
                    (map 
                        (fun (u : field SS.type) => 
                            (fst u, (EPrj r (fst u)))) 
                        us))
        | SS.st_rec_depth ss _ HS =>
            let fix rechelp {ss' ts' : fields SS.type} 
                (HS' : relfs SS.subtype ss' ts') : fields expr :=
                match HS' with
                | Forall2_nil _ => []
                | Forall2_cons s _ (conj _ Hst) Hssts =>
                    (fst s, EApp (translate_subtype Hst) (EPrj r (fst s))) :: (rechelp Hssts)
                end in
            EFun "r" (TRec (map (map_snd translate_type) ss)) (ERec (rechelp HS))
        end.

    (* Coq is making me define this as a relation instead of a function... *)
    Inductive translate_subtype : forall {s t : SST.type}, 
    SS.subtype s t -> expr -> Prop :=
        | ts_refl : forall (t : SST.type),
            translate_subtype (SS.st_refl t)
                (EFun "x" (translate_type t) (EVar "x"))
        | ts_trans : forall (s u t : SST.type) (e1 e2 : expr)
            (C1 : SS.subtype s u) (C2 : SS.subtype u t),
            translate_subtype C1 e1 ->
            translate_subtype C2 e2 ->
            translate_subtype
                (SS.st_trans s u t C1 C2)
                (EFun "x" (translate_type s) 
                    (EApp e2 (EApp e1 (EVar "x"))))
        | ts_top : forall (t : SST.type),
            translate_subtype (SS.st_top t)
                (EFun "x" (translate_type t) EUnit)
        | ts_fun : forall (s1 t1 s2 t2 : SST.type) (e1 e2: expr)
            (C1 : SS.subtype t1 s1) (C2 : SS.subtype s2 t2),
            translate_subtype C1 e1 ->
            translate_subtype C2 e2 ->
            translate_subtype 
                (SS.st_fun s1 t1 s2 t2 C1 C2)
                (EFun "f" (translate_type (SST.TFun s1 s2 ))
                    ((EFun "x") (translate_type t1)
                        (EApp e2 (EApp (EVar "f") (EApp e1 (EVar "x"))))))
        | ts_rec_width : forall (us vs : fields SST.type),
            translate_subtype
                (SS.st_rec_width us vs)
                (EFun "r" 
                    (TRec (map (map_snd translate_type) (us ++ vs)))
                    (ERec 
                        (map 
                            (fun (u : field SST.type) => 
                                (fst u, (EPrj (EVar "r") (fst u)))) 
                            us)))
        | ts_rec_depth : forall (ss ts : fields SST.type)
            (HS : relfs SS.subtype ss ts) (es : fields expr),
            map fst ss = map fst es ->
            (forall (s : field SST.type) (t : field SST.type),
            exists (H : SS.subtype (snd s) (snd t)),
            In (s,t) (combine ss ts) ->
            exists (e : field expr), translate_subtype H (snd e) /\
            In (s,e) (combine ss es)) ->
            translate_subtype
                (SS.st_rec_depth ss ts HS)
                (EFun "r" 
                    (TRec (map (map_snd translate_type) ss)) 
                    (ERec (map (fun e => 
                        (fst e, EApp (snd e) (EPrj (EVar "r") (fst e)))) es)))
        | ts_rec_perm : forall (ss ts : fields SST.type) (HP : perm ss ts),
            translate_subtype 
                (SS.st_rec_perm ss ts HP)
                (EFun "r" 
                    (TRec (map (map_snd translate_type) ss))
                    (ERec 
                        (map 
                            (fun (lbl : field SST.type) => 
                                (fst lbl, (EPrj (EVar "r") (fst lbl)))) 
                            ss))).

    Lemma translate_subtype_correct :
        forall {s t : SST.type} (C : SS.subtype s t) (e : expr),
        translate_subtype C e ->
        forall (g : gamma),
        check g e (TFun (translate_type s) (translate_type t)).
    Proof.
        intros s t C e TST. dependent induction TST; intros g.
        - constructor. constructor. reflexivity.
        - remember (translate_type s) as s' in *.
            remember (translate_type u) as u' in *.
            remember (translate_type t) as t' in *.
            constructor.
            apply check_app with (t := u').
            + apply IHTST2.
            + apply check_app with (t := s').
                * apply IHTST1.
                * constructor. reflexivity.
        - constructor. constructor.
        - simpl. remember (translate_type s1) as s1' in *.
            remember (translate_type s2) as s2' in *.
            remember (translate_type t1) as t1' in *.
            remember (translate_type t2) as t2' in *. 
            constructor. constructor.
            apply check_app with (t := s2').
            + apply IHTST2.
            + apply check_app with (t := s1');
                try (constructor; reflexivity).
                apply check_app with (t := t1');
                try (constructor; reflexivity).
                apply IHTST1.
        - constructor. simpl. constructor.
            induction us; constructor.
            + destruct a as [a1 a2]; split; simpl;
                try reflexivity.
                apply check_prj with 
                    (ts := ((ID a1, translate_type a2)
                        :: map (map_snd translate_type) (us ++ vs))).
                * constructor. reflexivity.
                * constructor. reflexivity.
            + simpl. admit.
                (* Requires a helper lemma for how adding 
                    field to a record type bound to a variable
                    in the context doesn't change
                    typing projections. *)
        - constructor. constructor. admit.
            (* requires a stronger induction 
                hypothesis for translate_subtype. *)
        - constructor. constructor.
            fold translate_type.
            dependent induction HP.
            + constructor.
            + destruct x as [x1 x2].
                constructor.
                * split; try reflexivity. simpl.
                    apply check_prj with 
                        (ts := ((ID x1, translate_type x2) 
                            :: map (map_snd translate_type) l));
                    constructor; reflexivity.
                * simpl. admit.
                (* Requires a helper lemma for how adding 
                    field to a record type bound to a variable
                    in the context doesn't change
                    typing projections. *)
            + destruct x as [x1 x2].
                destruct y as [y1 y2].
                constructor; simpl.
                { split.
                    - admit.
                        (* This case baffles me... *)
                    - simpl. apply check_prj with
                        (ts := ((ID y1, translate_type y2)
                        :: (ID x1, translate_type x2) 
                            :: map (map_snd translate_type) l)).
                        + constructor. admit.
                            (* I don't understand 
                                what is going on... *) 
                        + constructor. reflexivity. }
                { constructor.
                    - split; simpl.
                        + admit.
                            (* Why Coq, why? *)
                        + apply check_prj with
                            (ts := (ID y1, translate_type y2)
                                :: (ID x1, translate_type x2) 
                                :: map (map_snd translate_type) l).
                            * admit.
                                (* I don't get it... *)
                            * constructor. reflexivity. }
            + admit.
                (* I don't feel like doing this... *)
    Admitted.

    Definition translate_gamma (g : @gamma SST.type) (x : id) :=
        match g x with
        | None => None
        | Some t => Some (translate_type t)
        end.

    Lemma translate_gamma_bind :
        forall (g : gamma) (x : id) (t : SST.type),
        translate_gamma (bind x t g) = 
            bind x (translate_type t) (translate_gamma g).
    Proof.
        intros g x t. apply functional_extensionality.
        intros y. unfold translate_gamma.
        destruct (IdDec.eq_dec x y).
        - subst. rewrite bind_correct.
            rewrite bind_correct. reflexivity.
        - unfold bind.
            apply eqb_neq in n. rewrite n. reflexivity.
    Qed.

    Inductive translate_expr {g : @gamma SST.type} :
    forall {e : SSE.expr} {t : SST.type},
    SS.check g e t -> expr -> Prop :=
        | te_unit : 
            forall (H : SS.check g SSE.EUnit SST.TUnit),
            translate_expr H EUnit
        | te_var : forall (x : id) (t : SST.type) 
            (H : SS.check g (SSE.EVar x) t),
            g x = Some t ->
            translate_expr H (EVar x)
        | te_fun : forall (x : id) (t1 t2 : SST.type) 
            (e : SSE.expr) (e' : expr)
            (D2 : SS.check (bind x t1 g) e t2)
            (H : SS.check g (SSE.EFun x t1 e) (SST.TFun t1 t2)),
            @translate_expr (bind x t1 g) e t2 D2 e' ->
            translate_expr H (EFun x (translate_type t1) e')
        | te_app : forall (e1 e2 : SSE.expr) 
            (t11 t12 : SST.type) (e1' e2' : expr)
            (D1 : SS.check g e1 (SST.TFun t11 t12))
            (D2 : SS.check g e2 t11)
            (H : SS.check g (SSE.EApp e1 e2) t12),
            translate_expr D1 e1' ->
            translate_expr D2 e2' ->
            translate_expr H (EApp e1' e2')
        (* Skipping translation for records...for now! *)
        | te_prj : forall (e : SSE.expr) (x : id) 
            (t : SST.type) (ts : fields SST.type) (e' : expr)
            (D1 : SS.check g e (SST.TRec ts))
            (H : SS.check g (SSE.EPrj e x) t),
            In (x,t) ts ->
            translate_expr D1 e' ->
            translate_expr H (EPrj e' x)
        | te_subsume : forall (e : SSE.expr) (s t : SST.type) (d' c' : expr)
            (D : SS.check g e s) (C : SS.subtype s t)
            (H : SS.check g e t),
            translate_subtype C c' ->
            translate_expr D d' ->
            translate_expr H (EApp c' d').

    Theorem translate_expr_correct :
        forall {g : @gamma SST.type} {e : SSE.expr} {t : SST.type}
        (D : SS.check g e t) (e' : expr),
        translate_expr D e' -> 
        check (translate_gamma g) e' (translate_type t).
    Proof.
        intros g e t D e' TE. 
            dependent induction TE.
        - constructor.
        - constructor. unfold translate_gamma.
            rewrite H0. reflexivity.
        - constructor. fold translate_type.
            rewrite <- translate_gamma_bind.
            assumption.
        - simpl in *. remember (translate_type t11) as t11' in *.
            remember (translate_type t12) as t12' in *.
            apply check_app with (t := t11'); assumption.
        - simpl in *.
            remember (map (map_snd translate_type) ts) as ts' in *.
            apply check_prj with (ts := ts'); auto. subst.
            assert (dumb : (x, translate_type t)
                = (map_snd translate_type) (x,t));
            try reflexivity.
            rewrite dumb. apply in_map. assumption.
        - remember (translate_type s) as s' in *.
            remember (translate_type t) as t' in *.
            apply check_app with (t := s'); auto. subst. 
            apply translate_subtype_correct with (C0 := C).
            assumption.
    Qed.

    (* Below definition is incorrect :
        e1' and e2' should evaluate to
        the same value but they may not be equal *)
    Theorem Coherence :
        forall {g : @gamma SST.type} {e : SSE.expr} {t : SST.type}
        (D1 D2 : SS.check g e t) (e1' e2' : expr),
        translate_expr D1 e1' ->
        translate_expr D2 e2' -> e1' = e2'.
    Proof.
    Abort.
End Coercion.

Module AlgorithmicSubtyping.
    Module SS := SubsumptionSTLC.
    Import SS.SSType.
    Import SS.SSExpr.
    Import SS.Step.

    Inductive subtype : type -> type -> Prop :=
        | st_top : forall (s : type), subtype s TTop
        | st_unit : subtype TUnit TUnit
        | st_fun : forall (s1 s2 t1 t2 : type),
            subtype t1 s1 ->
            subtype s2 t2 ->
            subtype (TFun s1 s2) (TFun t1 t2)
        | st_rec : forall (ss ts : fields type),
            (forall (t : field type),
            In t ts -> 
            exists (s : field type),
            In s ss /\ relf subtype s t) ->
            subtype (TRec ss) (TRec ts).

    Section SubtypeInduction.
        Variable P : type -> type -> Prop.

        Hypothesis HTop : forall t, P t TTop.

        Hypothesis HUnit : P TUnit TUnit.

        Hypothesis HFun : forall s1 s2 t1 t2,
            subtype t1 s1 -> P t1 s1 ->
            subtype s2 t2 -> P s2 t2 ->
            P (TFun s1 s2) (TFun t1 t2).

        Hypothesis HRec : forall (ss ts : fields type),
            (forall t : field type, In t ts -> 
                exists s : field type, In s ss /\ relf subtype s t) ->
            (forall t : field type, In t ts -> 
                exists s : field type, In s ss /\ relf P s t) ->
            P (TRec ss) (TRec ts).

        Fixpoint IHSubtype (s t : type) (HS : subtype s t) : P s t.
        Proof.
            destruct HS.
            - apply HTop.
            - apply HUnit.
            - apply HFun; auto.
            - apply HRec; auto. intros t Hintts.
                apply H in Hintts as [s [Hinss HRst]].
                exists s. split; auto.
                destruct HRst as [Hfst HSst].
                split; auto.
        Qed.
    End SubtypeInduction.

    Lemma Reflexive :
        forall (t : type),
        subtype t t.
    Proof.
        intros t. induction t using IHType;
        constructor; auto.
        intros t Hin. exists t. split; auto.
        pose proof Forall_forall 
            (predf (fun t => subtype t t)) fs as FF.
        unfold predfs in H. destruct FF as [F1 _].
        apply F1 with (x := t) in H; auto.
        split; auto.
    Qed.

    Lemma st_fields_refl :
        forall (fs : fields type),
        relfs subtype fs fs.
    Proof.
        intros fs. induction fs; constructor.
        - split; auto. apply Reflexive.
        - assumption.
    Qed.

    Lemma Transitive :
        forall (s u t : type),
        subtype s u -> subtype u t -> subtype s t.
    Proof.
        intros s u.
        generalize dependent s.
        induction u using IHType;
        intros s t Hsu Hut.
        - inv Hut. constructor.
        - inv Hsu. assumption.
        - inv Hsu. inv Hut; constructor.
            + apply IHu1; auto.
            + apply IHu2; auto.
        - inv Hsu. inv Hut; constructor;
            intros t Hintts.
            apply H1 in Hintts 
                as [s [Hinsss HRst]]; clear H1.
            apply H2 in Hinsss as H2'.
            destruct H2' as [u [Hinuss HRus]].
            exists u. split; auto.
            pose proof Forall_forall 
            (predf (fun u : type =>
                forall s t : type, subtype s u -> 
                subtype u t -> subtype s t)) fs as [F1 _].
            apply F1 with (x := s) in H; auto; clear F1.
            unfold predf in H.
            destruct s as [s st].
            destruct u as [u ut].
            destruct t as [t tt].
            destruct HRus as [HFus HSus].
            destruct HRst as [HFst HSst]. 
            simpl in *. subst. split; auto.
    Qed.

    Theorem Subtyping_Complete :
        forall (s t : type),
        SS.subtype s t -> subtype s t.
    Proof.
        intros s t HS.
        dependent induction HS using SS.IHSubtype.
        - apply Reflexive.
        - apply Transitive with (u := u); auto.
        - constructor.
        - constructor; auto.
        - constructor. intros t Hintus.
            exists t. split.
            + apply in_or_app. left.
                assumption.
            + split; auto.
                apply Reflexive.
        - constructor. intros t Hinvs.
            apply relfs_in_exists_r with (vs0 := vs); auto.
        - constructor. intros t Hinvs.
            exists t. split.
            + apply Permutation_in with (l := vs); auto.
                apply Permutation_sym; auto.
            + split; auto. apply Reflexive.
    Qed.

    (* NOTE: This proofs relies upon
        an unproven assumption
        about recording subtyping
        in the declarative definition.
        See rec_subtype_equiv.
        *)
    Theorem Subtyping_Sound :
        forall (s t : type),
        subtype s t -> SS.subtype s t.
    Proof.
        intros s t HS.
        dependent induction HS using IHSubtype.
        - constructor.
        - constructor.
        - constructor; auto.
        - apply st_rec in H as HR.
            apply SS.alt_rec_subtyping; auto.
    Qed.

    Ltac oblige :=
        repeat split;
        try (intros [HF1 HF2]; discriminate);
        try (intros s1 s2 t1 t2 [HF1 HF2]; discriminate);
        try (intros ss [HF1 HF2]; discriminate);
        try (intros hs ts ht tt [HF1 HF2]; discriminate);
        try (intros w [HF1 HF2]; discriminate).

    Program Fixpoint is_subtype (s t : type) 
    {measure ((type_nat s) + (type_nat t))} : bool :=
        match s, t with
        | _, TTop 
        | TUnit, TUnit => true
        | TFun s1 s2, TFun t1 t2 =>
            is_subtype t1 s1 && is_subtype s2 t2
        | TRec ss, TRec [] => true
        | TRec (heads::tails), TRec (headt::tailt) =>
            if (fst heads =? fst headt)%string
                then if is_subtype (snd heads) (snd headt)
                    then is_subtype (TRec tails) (TRec tailt)
                    else false
                else if is_subtype (TRec tails) (TRec [headt])
                    then is_subtype (TRec (heads::tails)) (TRec tailt)
                    else false
        | _, _ => false
        end.
    (* Solve Obligations of is_subtype with oblige. *)
    (* Solve Obligations with omega. *)
    Next Obligation.
    Proof. simpl. omega. Qed.
    Next Obligation.
    Proof. simpl. omega. Qed.
    Next Obligation.
    Proof. simpl. omega. Qed.
    Next Obligation.
    Proof. 
        simpl. remember
            (fold_right
                (fun (t' : id * type) (n : nat) =>
                    type_nat (snd t') + n) 0 tailt)
            as help in *.
        pose proof type_nat_pos (snd heads)
            as [ns Hns]. rewrite Hns.
        pose proof type_nat_pos (snd headt)
            as [nt Hnt]. rewrite Hnt. omega.
    Qed.
    Next Obligation.
    Proof. 
        simpl. remember
            (fold_right
                (fun (t' : id * type) (n : nat) =>
                    type_nat (snd t') + n) 0 tailt)
            as help in *.
        pose proof type_nat_pos (snd heads)
            as [ns Hns]. rewrite Hns.
        pose proof type_nat_pos (snd headt)
            as [nt Hnt]. rewrite Hnt. omega.
    Qed.
    Next Obligation.
    Proof.
        simpl. remember
            (fold_right
                (fun (t' : id * type) (n : nat) =>
                    type_nat (snd t') + n) 0 tailt)
            as help in *.
        pose proof type_nat_pos (snd heads)
            as [ns Hns]. rewrite Hns.
        pose proof type_nat_pos (snd headt)
            as [nt Hnt]. rewrite Hnt. omega.
    Qed.
    Solve All Obligations with oblige.

    (* Per usual, the record case is unwieldy. *)
    Fixpoint SubtypeDec (s t : type) :
        {subtype s t} + {~ subtype s t}.
    Proof.
        destruct s; destruct t;
        try (left; apply st_top);
        try (right; intros HF; inv HF; contradiction).
        - left. constructor.
        - destruct (SubtypeDec t1 s1) as [H1 | H1];
            destruct (SubtypeDec s2 t2) as [H2 | H2];
            try (right; intros HF; inv HF; contradiction).
            left. constructor; auto.
        - generalize dependent fs0.
            induction fs; intros gs; destruct gs.
            + left. constructor. intros t H. inv H.
            + right. intros HF. inv HF.
                assert (Hinfgs : In f (f :: gs));
                try apply in_eq.
                apply H1 in Hinfgs as [s [Hinse _]].
                inv Hinse.
            + left. constructor. intros t H. inv H.
            + destruct a as [xa ta];
                destruct f as [xf tf]. 
                destruct (IHfs gs) as [IH | IH];
                destruct (IdDec.eq_dec xa xf) as [HX | HX];
                destruct (SubtypeDec ta tf) as [HS | HS]; subst.
                * left. constructor. intros t Hin.
                    admit.
    Admitted.
End AlgorithmicSubtyping.