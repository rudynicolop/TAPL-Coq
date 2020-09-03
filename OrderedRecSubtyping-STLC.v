(* In Subsumption-STLC I defined an
    STLC extended with records and 
    subtyping, and proved 
    progress and preservation
    with the declarative rules.

    However, proving an algorithmic
    definition of subtyping sound and
    complete with respect to the declarative
    definition proved fruitless.

    Here is an attempt where record-subtyping
    is restricted in that common field names
    must be in the same order. *)

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
Require Import Coq.Program.Equality.

Ltac inv H := inversion H; subst.

Ltac injintrosubst H := injection H; intros; subst.

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

    Definition relf {U V : Type} (R : U -> V -> Prop) (u : field U) (v : field V) : Prop :=
        (fst u) = (fst v) /\ R (snd u) (snd v).

    Definition relfs {U V : Type} (R : U -> V -> Prop) : fields U -> fields V -> Prop :=
        Forall2 (relf R).

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

Module Declarative.
    Module Types.
        Inductive type : Type :=
            | TTop
            | TUnit
            | TFun (t t' : type)
            | TRec (fs : fields type).

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
    End Types.
    Export Types.
    
    Module Expr.
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
    End Expr.
    Export Expr.

    Module Subtype.
        (* The Subtyping Relation 
            disallowing permutations *)
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
                end.
        End SubtypeInduction.

        Lemma st_fields_refl :
            forall (fs : fields type), relfs subtype fs fs.
        Proof. 
            induction fs; constructor.
            - split; constructor.
            - assumption.
        Qed.

        Example record_subtyping_makes_sense :
            subtype 
                (TRec [("x",TUnit);("y",TUnit)]) 
                (TRec [("x",TTop)]).
        Proof.
            apply st_trans with (u := TRec [("x",TUnit)]).
            - assert (HE : [("x", TUnit); ("y", TUnit)] 
                = [("x", TUnit)] ++ [("y", TUnit)]);
                try reflexivity. rewrite HE.
                    apply st_rec_width.     
            - apply st_rec_depth. constructor.
                + split; auto. apply st_top.
                + constructor.
        Qed.

        (* This is in true in the relation
            with permutations. However it is
            false under this relation. *)
        Example record_subtyping_limitation :
            subtype 
                (TRec [("x",TUnit);("y",TUnit)]) 
                (TRec [("y",TTop)]).
        Proof.
            apply st_trans with (u := TRec [("y",TUnit)]).
            (* stuck here, no permutation *)
        Abort.

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
            Qed.
        End InvSubsumption.
    End Subtype.
    Export Subtype.
End Declarative.

Module Algorithmic.
    Module D := Declarative.
    Import D.Types.
    Import D.Expr.
    Module SS := D.Subtype.

    Module Subtype.
        Inductive subtype : type -> type -> Prop :=
            | st_top : forall (s : type), subtype s TTop
            | st_unit : subtype TUnit TUnit
            | st_fun : forall (s1 s2 t1 t2 : type),
                subtype t1 s1 ->
                subtype s2 t2 ->
                subtype (TFun s1 s2) (TFun t1 t2)
            | st_rec_nil : forall (ss : fields type),
                subtype (TRec ss) (TRec [])
            | st_rec_cons : 
                forall (x : id) (hs ht : type) (ss ts : fields type),
                subtype hs ht ->
                subtype (TRec ss) (TRec ts) ->
                subtype (TRec ((x,hs)::ss)) (TRec ((x,ht)::ts)).

        Lemma Reflexive :
            forall (t : type),
            subtype t t.
        Proof.
            intros t. induction t using IHType;
            try constructor; auto.
            induction fs.
            - constructor.
            - inv H. destruct a. apply st_rec_cons; auto.
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
            - generalize dependent t.
                generalize dependent s.
                induction H; 
                intros s Hsu t Hut;
                inv Hsu; inv Hut;
                try apply st_top;
                try apply st_rec_nil.
                constructor; auto.            
        Qed.

        Theorem Complete :
            forall (s t : type),
            SS.subtype s t -> subtype s t.
        Proof.
            intros s t HS.
            dependent induction HS using SS.IHSubtype.
            - apply Reflexive.
            - apply Transitive with (u := u); auto.
            - constructor.
            - constructor; auto.
            - induction us; simpl;
                try constructor.
                destruct a. constructor; auto.
                apply Reflexive.
            - induction H0; try constructor; inv H; auto.
                destruct x as [x xt].
                destruct y as [y yt].
                inv H5. inv H0. simpl in *. subst.
                constructor; auto.
        Qed.

        Theorem Subtyping_Sound :
            forall (s t : type),
            subtype s t -> SS.subtype s t.
        Proof.
            intros s t HS.
            dependent induction HS.
            - constructor.
            - constructor.
            - constructor; auto.
            - apply SS.subtype_empty_rec.
            - apply SS.cons_subtype_rec; auto.
                split; auto. 
        Qed.
    End Subtype.
End Algorithmic.