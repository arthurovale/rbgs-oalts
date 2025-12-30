Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Alts.
Require Import oalts.Sig.
Require Import Coq.Logic.FunctionalExtensionality.
From Paco Require Import paco.

Module OALTSBase. (* <: Category. *)
  Import AsyncEvents.
  Import Sig.
  Import ALTS.

  Definition oalts (A B : sig) := alts ([A -o B])%event_obj.

  Definition compose {A B C : sig} (τ : oalts B C) (σ : oalts A B) : oalts A C :=
    {|
      states := states σ * states τ;
      start := fun s => start σ (fst s) /\ start τ (snd s);
      trans := fun s ev s' =>
        (exists evs evt,
          (projR evs = projL evt /\ projL evs = ext projL ev /\ projR evt = ext projR ev) /\
          (σ (fst s) ('evs) (fst s') /\ τ (snd s) ('evt) (snd s'))) \/
        (exists evs,
          (ext projR evs = ɛ /\ ext projL evs = ext projL ev /\ ɛ = ext projR ev) /\
          (trans σ (fst s) evs (fst s') /\ snd s = snd s')) \/
        (exists evt,
          (ɛ = ext projL evt /\ ɛ = ext projL ev /\ ext projR evt = ext projR ev) /\
          (fst s = fst s' /\ trans τ (snd s) evt (snd s')));
    |}.

  Local Open Scope event_obj_scope.
  Definition id (A : sig) : oalts A A :=
    {|
      states := unit;
      start := fun _ => True;
      trans := fun _ ev _ =>
        match ev with
        | 'neg ⟨an | bn⟩ => an = bn
        | 'pos ⟨ap | bp⟩ => ap = bp
        | _ => False
        end
    |}.

  Section Id_Aux.

    Lemma id_trans_iff {A : sig} {ev : Async [A -o A]} {s s' : states (id A)} :
      id A s ev s' <-> 
        exists ev', ev = 'ev' /\ projL ev' = projR ev'.
    Proof.
      split.
      - intros.
        destruct ev as [ev'| ]; [| contradiction].
        exists ev'. simpl in H. destruct ev' as [ev' | ev'].
        all: split; [reflexivity | ].
        all: destruct ev'; subst; try reflexivity; try contradiction.
      - intros; simpl. destruct H as [ev' [Hvis Heq]].
        rewrite Hvis. destruct ev' as [ev' | ev']; destruct ev';
        simpl in Heq; try unfold_proj in Heq;
        inversion Heq; reflexivity.
    Qed.

    Lemma id_weak_trans {A : sig} : forall s ev s',
      weak_trans (id A) s ev s' <-> trans (id A) s ('ev) s'.
    Proof.
      intros [] ev []. split. 
      - intros H. destruct H as [[] [Hstar Hid]]. exact Hid.
      - intros Hid. exists tt. split. 
        apply tau_refl. exact Hid.
    Qed.

  End Id_Aux.

  Section Compose_Id_Left.

    Definition compose_id_rel {A B : sig} (σ : oalts A B) 
      (s1 : states (compose (id B) σ)) (s2 : states σ) : Prop :=
      tau_star σ s2 (fst s1) /\ snd s1 = tt.

    (** Prove it's a simulation in one direction *)
    Lemma compose_id_rel_sim {A B : sig} (σ : oalts A B) :
      forall s1 s2, compose_id_rel σ s1 s2 ->
        alts_simF (compose (id B) σ) σ (compose_id_rel σ) s1 s2.
    Proof.
      intros [s []] s2 [Hstar Htt]. simpl in Htt. subst.
      split.
      - (* Visible case: compose does s --'ev--> t *)
        intros ev [t []] Htrans.
        exists t. split.
        + (* weak_trans: σ matches via tau_star then visible *)
          exists s. split; [eapply tau_star_trans; [exact Hstar | constructor] |].
          destruct Htrans as [[evs [evt [Heqs [Hσ Hid]]]] |
                            [[evs [Heqs [Hσ _]]] | [evt [Heqs [_ Hid]]]]].
          * (* Sync case: evs = ev via projections *)
            apply id_trans_iff in Hid. destruct Hid as [ev' [Heq Hproj]].
            destruct Heqs as [Hmatch [HprojL HprojR]]. simpl in *.
            injection Heq as Heq'. rewrite <- Heq' in Hproj.
            rewrite (projL_ProjR_eq HprojL (eq_trans Hmatch (eq_trans Hproj HprojR))) in Hσ.
            exact Hσ.
          * (* Left-only case *)
            destruct Heqs as [HprojR [HprojL Heps]]. simpl in *.
            destruct evs as [evs |]; [| exfalso; eapply projL_projR_eps; symmetry; [exact HprojL | exact Heps]].
            simpl in HprojR. rewrite (projL_ProjR_eq HprojL (eq_trans HprojR Heps)) in Hσ. exact Hσ.
          * (* Right-only case: contradiction *)
            apply id_trans_iff in Hid. destruct Hid as [ev' [Heq Hproj]].
            rewrite Heq in Heqs. destruct Heqs as [HprojL _]. simpl in *.
            rewrite <- HprojL in Hproj.
            exfalso. eapply projL_projR_eps; symmetry; [exact HprojL | exact Hproj].
        + split; [constructor | reflexivity].
      - (* Tau case: compose does s --ɛ--> t *)
        intros [t []] Htrans.
        destruct Htrans as [[evs [evt [Heqs [_ Hid]]]] |
                          [[evs [Heqs [Hσ Heq]]] | [evt [Heqs [_ Hid]]]]].
        + (* Sync: contradiction *)
          apply id_trans_iff in Hid. destruct Hid as [ev' [Heq Hproj]].
          destruct Heqs as [Hmatch [HprojL HprojR]]. simpl in *.
          injection Heq as Heq'. rewrite <- Heq' in Hproj. exfalso.
          eapply projL_projR_eps; [exact HprojL | rewrite Hmatch, Hproj; exact HprojR].
        + (* Left-only: σ tau step *)
          destruct Heqs as [HprojR [HprojL _]]. simpl in *.
          destruct evs as [ev' |]; [exfalso; eapply projL_projR_eps; [exact HprojL | exact HprojR] |].
          simpl in Hσ. subst. split; [| reflexivity].
          eapply tau_star_trans; [exact Hstar | econstructor; [exact Hσ | constructor]].
        + (* Right-only: contradiction *)
          destruct Heqs as [HprojL [_ HprojR]]. simpl in *.
          destruct evt as [ev' |]; [exfalso; eapply projL_projR_eps; [symmetry; exact HprojL | exact HprojR] |].
          simpl in Hid. contradiction.
    Qed.

    Lemma compose_id_left_forward {A B} (σ : oalts A B) :
      forall s, alts_sim' (compose (id B) σ) σ (s, tt) s.
    Proof.
      intros s.
      apply (alts_sim_coind (compose (id B) σ) σ (compose_id_rel σ) (compose_id_rel_sim σ)).
      split; [constructor | reflexivity].
    Qed.

    (** Relation for backward simulation: σ can be "ahead" via taus *)
    Definition compose_id_rel_back {A B : sig} (σ : oalts A B)
      (s1 : states σ) (s2 : states (compose (id B) σ)) : Prop :=
      tau_star σ (fst s2) s1 /\ snd s2 = tt.

    (** Prove backward simulation via coinduction *)
    Lemma compose_id_rel_back_sim {A B : sig} (σ : oalts A B) :
      forall s1 s2, compose_id_rel_back σ s1 s2 ->
        alts_simF σ (compose (id B) σ) (compose_id_rel_back σ) s1 s2.
    Proof.
      intros s1 [s2 []] [Hstar Htt]. simpl in *. subst.
      split.
      - (* Visible case: σ does s1 --'ev--> s1' *)
        intros ev s1' Htrans.
        (* compose can catch up via taus then do the visible transition *)
        exists (s1', tt). split.
        + (* weak_trans: compose does tau_star then visible *)
          exists (s1, tt). split.
          * (* tau_star from (s2, tt) to (s1, tt) by propagating σ's taus *)
            clear Htrans. induction Hstar as [| s0 s1_mid s1_end Hstep Hstar' IHstar].
            -- constructor.
            -- eapply tau_step; [| exact IHstar].
              right. left. exists ɛ. simpl.
              repeat split; exact Hstep.
          * (* visible transition (s1, tt) --'ev--> (s1', tt) *)
            destruct (projR ev) as [b | ] eqn:HprojR.
            -- (* B component: sync with id *)
              left. exists ev.
              destruct b as [bm | bp].
              ++ exists (neg ⟨bm | bm⟩). simpl. repeat split; auto.
              ++ exists (pos ⟨bp | bp⟩). simpl. repeat split; auto.
            -- (* No B component: σ-only *)
              right. left. exists ('ev). simpl. repeat split; auto.
        + (* Relation preserved: tau_star σ s1' s1' *)
          split; [constructor | reflexivity].
      - (* Tau case: σ does s1 --ɛ--> s1' *)
        intros s1' Htrans.
        (* σ advances, compose stays, relation still holds by transitivity *)
        split; [| reflexivity].
        eapply tau_star_trans; [exact Hstar | econstructor; [exact Htrans | constructor]].
    Qed.

    Lemma compose_id_left_backward {A B : sig} (σ : oalts A B) :
      forall (s : states σ), alts_sim' σ (compose (id B) σ) s (s, tt).
    Proof.
      intros s.
      apply (alts_sim_coind σ (compose (id B) σ) (compose_id_rel_back σ) (compose_id_rel_back_sim σ)).
      split; [constructor | reflexivity].
    Qed.

    Proposition compose_id_left :
      forall {A B} (σ : oalts A B), compose (id B) σ ≈ σ.
    Proof.
      intros A B σ. split.
      - intros [s []] [Hstart_σ _].
        exists s. split; [exact Hstart_σ |].
        apply compose_id_left_forward.
      - intros s Hstart_σ.
        exists (s, tt). split; [split; [exact Hstart_σ | exact I] |].
        apply compose_id_left_backward.
    Qed.
    
  End Compose_Id_Left.

  Section Compose_Id_Right.

    Definition compose_id_rel_r {A B : sig} (σ : oalts A B)
      (s1 : states (compose σ (id A))) (s2 : states σ) : Prop :=
      tau_star σ s2 (snd s1) /\ fst s1 = tt.

    (** Prove it's a simulation in one direction *)
    Lemma compose_id_rel_r_sim {A B : sig} (σ : oalts A B) :
      forall s1 s2, compose_id_rel_r σ s1 s2 ->
        alts_simF (compose σ (id A)) σ (compose_id_rel_r σ) s1 s2.
    Proof.
      intros [[] s] s2 [Hstar Htt]. simpl in Htt. subst.
      split.
      - (* Visible case: compose does s --'ev--> t *)
        intros ev [[] t] Htrans.
        exists t. split.
        + (* weak_trans: σ matches via tau_star then visible *)
          exists s. split; [eapply tau_star_trans; [exact Hstar | constructor] |].
          destruct Htrans as [[evs [evt [Heqs [Hid Hσ]]]] |
                             [[evs [Heqs [Hid _]]] | [evt [Heqs [_ Hσ]]]]].
          * (* Sync case: evt = ev via projections *)
            apply id_trans_iff in Hid. destruct Hid as [ev' [Heq Hproj]].
            destruct Heqs as [Hmatch [HprojL HprojR]]. simpl in *.
            injection Heq as Heq'. rewrite <- Heq' in Hproj.
            rewrite (projL_ProjR_eq (eq_trans (eq_sym Hmatch) (eq_trans (eq_sym Hproj) HprojL)) HprojR) in Hσ.
            exact Hσ.
          * (* Left-only case: contradiction *)
            apply id_trans_iff in Hid. destruct Hid as [ev' [Heq Hproj]].
            rewrite Heq in Heqs. destruct Heqs as [HprojRε _]. simpl in *.
            rewrite HprojRε in Hproj.
            exfalso. eapply projL_projR_eps; [exact Hproj | exact HprojRε].
          * (* Right-only case *)
            destruct Heqs as [HprojL [Heps HprojR]]. simpl in *.
            destruct evt as [evt |]; [| exfalso; eapply projL_projR_eps; [symmetry; exact Heps | symmetry; exact HprojR]].
            simpl in HprojL, HprojR.
            rewrite (projL_ProjR_eq (eq_trans (eq_sym HprojL) Heps) HprojR) in Hσ. exact Hσ.
        + split; [constructor | reflexivity].
      - (* Tau case: compose does s --ɛ--> t *)
        intros [[] t] Htrans.
        destruct Htrans as [[evs [evt [Heqs [Hid _]]]] |
                           [[evs [Heqs [Hid Heq]]] | [evt [Heqs [_ Hσ]]]]].
        + (* Sync: contradiction *)
          apply id_trans_iff in Hid. destruct Hid as [ev' [Heq Hproj]].
          destruct Heqs as [Hmatch [HprojL HprojR]]. simpl in *.
          injection Heq as Heq'. rewrite <- Heq' in Hproj. exfalso.
          eapply projL_projR_eps; [exact HprojL | rewrite <- Hproj; exact HprojL].
        + (* Left-only: contradiction *)
          destruct Heqs as [HprojR [HprojL _]]. simpl in *.
          destruct evs as [ev' |]; [exfalso; eapply projL_projR_eps; [exact HprojL | exact HprojR] |].
          simpl in Hid. contradiction.
        + (* Right-only: σ tau step *)
          destruct Heqs as [HprojL [_ HprojR]]. simpl in *.
          destruct evt as [ev' |]; [exfalso; eapply projL_projR_eps; [symmetry; exact HprojL | exact HprojR] |].
          simpl in Hσ. subst. split; [| reflexivity].
          eapply tau_star_trans; [exact Hstar | econstructor; [exact Hσ | constructor]].
    Qed.

    Lemma compose_id_right_forward {A B} (σ : oalts A B) :
      forall s, alts_sim' (compose σ (id A)) σ (tt, s) s.
    Proof.
      intros s.
      apply (alts_sim_coind (compose σ (id A)) σ (compose_id_rel_r σ) (compose_id_rel_r_sim σ)).
      split; [constructor | reflexivity].
    Qed.

    (** Relation for backward simulation: σ can be "ahead" via taus *)
    Definition compose_id_rel_r_back {A B : sig} (σ : oalts A B)
      (s1 : states σ) (s2 : states (compose σ (id A))) : Prop :=
      tau_star σ (snd s2) s1 /\ fst s2 = tt.

    (** Prove backward simulation via coinduction *)
    Lemma compose_id_rel_r_back_sim {A B : sig} (σ : oalts A B) :
      forall s1 s2, compose_id_rel_r_back σ s1 s2 ->
        alts_simF σ (compose σ (id A)) (compose_id_rel_r_back σ) s1 s2.
    Proof.
      intros s1 [[] s2] [Hstar Htt]. simpl in *. subst.
      split.
      - (* Visible case: σ does s1 --'ev--> s1' *)
        intros ev s1' Htrans.
        (* compose can catch up via taus then do the visible transition *)
        exists (tt, s1'). split.
        + (* weak_trans: compose does tau_star then visible *)
          exists (tt, s1). split.
          * (* tau_star from (tt, s2) to (tt, s1) by propagating σ's taus *)
            clear Htrans. induction Hstar as [| s0 s1_mid s1_end Hstep Hstar' IHstar].
            -- constructor.
            -- eapply tau_step; [| exact IHstar].
               right. right. exists ɛ. simpl.
               repeat split; exact Hstep.
          * (* visible transition (tt, s1) --'ev--> (tt, s1') *)
            destruct (projL ev) as [a | ] eqn:HprojL.
            -- (* A component: sync with id *)
               left.
               destruct a as [am | ap].
               ++ exists (neg ⟨am | am⟩), ev. simpl. repeat split; auto.
               ++ exists (pos ⟨ap | ap⟩), ev. simpl. repeat split; auto.
            -- (* No A component: σ-only *)
               right. right. exists ('ev). simpl. repeat split; auto.
        + (* Relation preserved: tau_star σ s1' s1' *)
          split; [constructor | reflexivity].
      - (* Tau case: σ does s1 --ɛ--> s1' *)
        intros s1' Htrans.
        (* σ advances, compose stays, relation still holds by transitivity *)
        split; [| reflexivity].
        eapply tau_star_trans; [exact Hstar | econstructor; [exact Htrans | constructor]].
    Qed.

    Lemma compose_id_right_backward {A B : sig} (σ : oalts A B) :
      forall (s : states σ), alts_sim' σ (compose σ (id A)) s (tt, s).
    Proof.
      intros s.
      apply (alts_sim_coind σ (compose σ (id A)) (compose_id_rel_r_back σ) (compose_id_rel_r_back_sim σ)).
      split; [constructor | reflexivity].
    Qed.

    Proposition compose_id_right :
      forall {A B} (σ : oalts A B), compose σ (id A) ≈ σ.
    Proof.
      intros A B σ. split.
      - intros [[] s] [_ Hstart_σ].
        exists s. split; [exact Hstart_σ |].
        apply compose_id_right_forward.
      - intros s Hstart_σ.
        exists (tt, s). split; [split; [exact I | exact Hstart_σ] |].
        apply compose_id_right_backward.
    Qed.

  End Compose_Id_Right.

  Section Compose_Assoc.

    Proposition compose_assoc :
      forall {A B C D} (σ : oalts A B) (τ : oalts B C) (ρ : oalts C D), 
        compose (compose ρ τ) σ  ≈ compose ρ (compose τ σ).  
    Admitted.

  End Compose_Assoc.

  Module StateLess. (* Functor *)
    Open Scope event_obj_scope.

    Definition StLess {A B : sig} (gen : Sig.m A B) : oalts A B :=
      {|
        states := unit;
        start := fun _ => True;
        trans := fun _ ev _ =>
          match ev with
          | 'neg ⟨an | bn⟩ => gen^- an = 'bn
          | 'pos ⟨ap | bp⟩ => gen^+ ap = 'bp
          | 'neg ⟨an | ⟩ => gen^- an = ɛ
          | 'pos ⟨ap | ⟩ => gen^+ ap = ɛ
          | _ => False
          end
      |}.

    (** Helper: weak_trans on StLess reduces to trans (states are trivial) *)
    Lemma StLess_weak_trans {A B} 
      (gen : Sig.m A B) (s : unit) (ev : [A -o B]) (s' : unit) :
      weak_trans (StLess gen) s ev s' <-> trans (StLess gen) s ('ev) s'.
    Proof.
      split.
      - intros [s'' [Hstar Htrans]].
        destruct s; destruct s'; destruct s''.
        exact Htrans.
      - intros Htrans. exists s. split.
        + constructor.
        + exact Htrans.
    Qed.

    (** Helper: weak_trans on composed StLess reduces to trans *)
    Lemma compose_StLess_weak_trans {A B C} (gen : Sig.m A B) (gen' : Sig.m B C)
        (s : unit * unit) (ev : [A -o C]) (s' : unit * unit) :
      weak_trans (compose (StLess gen') (StLess gen)) s ev s' <->
      trans (compose(StLess gen') (StLess gen)) s ('ev) s'.
    Proof.
      split.
      - intros [s'' [Hstar Htrans]].
        destruct s as [[] []], s'' as [[] []], s' as [[] []].
        exact Htrans.
      - intros Htrans. exists s. split.
        + constructor.
        + exact Htrans.
    Qed.

    (** Forward simulation helper *)
    Lemma StLess_compose_sim_forward {A B C : sig} (gen : Sig.m A B) (gen' : Sig.m B C) :
      forall (s : unit * unit),
        alts_sim' (compose (StLess gen') (StLess gen)) (StLess (gen' @ gen)) s tt.
    Proof.
      pcofix IH. intros [[] []].
      pfold. split.
      - (* Visible transitions *)
        intros ev [[] []] Htrans. simpl in Htrans.
        exists tt. split.
        + (* weak_trans on RHS *)
          apply StLess_weak_trans. simpl.
          (* Analyze the three cases from compose *)
          destruct Htrans as [[evs [evt [[Hmatch [HprojL HprojR]] [Hσ Hτ]]]] |
                             [[evs [[HprojRε [HprojL HprojRev]] [Hσ _]]] |
                              [evt [[HprojLε [HprojLev HprojR]] [_ Hτ]]]]]; simpl in *.
          * (* Sync case: both gen and gen' make visible transitions *)
            destruct evs as [evsm | evsp]; destruct evt as [evtm | evtp];
            simpl in Hmatch.
            -- (* Both negative: evsm and evtm *)
               destruct evsm as [am bm | am | bm]; destruct evtm as [bm' cm | bm' | cm];
               simpl in Hσ, Hτ, Hmatch; try contradiction; try discriminate;
               destruct ev as [evm | evp]; simpl in HprojL, HprojR;
               try destruct evm as [am' cm' | am' | cm'];
               try destruct evp as [ap' cp' | ap' | cp'];
               simpl in HprojL, HprojR; try discriminate;
               inversion Hmatch; subst; inversion HprojL; subst; inversion HprojR; subst;
               simpl; unfold Sig.compose; simpl; unfold AsyncEventsBase.compose;
               try (rewrite Hσ; exact Hτ); try (rewrite Hσ; simpl; exact Hτ).
            -- (* evsm negative, evtp positive: impossible by type *)
               destruct evsm as [am bm | am | bm]; destruct evtp as [bp' cp | bp' | cp];
               simpl in Hσ, Hτ, Hmatch; try contradiction; try discriminate.
            -- (* evsp positive, evtm negative: impossible by type *)
               destruct evsp as [ap bp | ap | bp]; destruct evtm as [bm' cm | bm' | cm];
               simpl in Hσ, Hτ, Hmatch; try contradiction; try discriminate.
            -- (* Both positive: evsp and evtp *)
               destruct evsp as [ap bp | ap | bp]; destruct evtp as [bp' cp | bp' | cp];
               simpl in Hσ, Hτ, Hmatch; try contradiction; try discriminate;
               destruct ev as [evm | evp]; simpl in HprojL, HprojR;
               try destruct evm as [am' cm' | am' | cm'];
               try destruct evp as [ap' cp' | ap' | cp'];
               simpl in HprojL, HprojR; try discriminate;
               inversion Hmatch; subst; inversion HprojL; subst; inversion HprojR; subst;
               simpl; unfold Sig.compose; simpl; unfold AsyncEventsBase.compose;
               try (rewrite Hσ; exact Hτ); try (rewrite Hσ; simpl; exact Hτ).
          * (* Left-only case: only gen makes a transition *)
            destruct evs as [evs' | ]; simpl in HprojRε, Hσ; try contradiction.
            destruct evs' as [evsm | evsp].
            -- destruct evsm as [am bm | am | bm];
               simpl in HprojRε, Hσ; try discriminate; try contradiction;
               destruct ev as [evm | evp];
               try destruct evm as [am' cm' | am' | cm'];
               try destruct evp as [ap' cp' | ap' | cp'];
               simpl in HprojL, HprojRev; try discriminate;
               inversion HprojL; subst;
               simpl; unfold Sig.compose; simpl; unfold AsyncEventsBase.compose;
               rewrite Hσ; reflexivity.
            -- destruct evsp as [ap bp | ap | bp];
               simpl in HprojRε, Hσ; try discriminate; try contradiction;
               destruct ev as [evm | evp];
               try destruct evm as [am' cm' | am' | cm'];
               try destruct evp as [ap' cp' | ap' | cp'];
               simpl in HprojL, HprojRev; try discriminate;
               inversion HprojL; subst;
               simpl; unfold Sig.compose; simpl; unfold AsyncEventsBase.compose;
               rewrite Hσ; reflexivity.
          * (* Right-only case: only gen' makes a transition - impossible *)
            destruct evt as [evt' | ]; simpl in Hτ, HprojLε; try contradiction.
            destruct evt' as [evtm | evtp].
            -- destruct evtm as [bm cm | bm | cm];
               simpl in Hτ, HprojLε; try discriminate; try contradiction.
            -- destruct evtp as [bp cp | bp | cp];
               simpl in Hτ, HprojLε; try discriminate; try contradiction.
        + right. apply IH.
      - (* Tau transitions - compose of StLess has no real tau transitions *)
        intros [[] []] Htrans. simpl in Htrans.
        destruct Htrans as [[evs [evt [[_ [HprojL _]] [Hσ _]]]] |
                           [[evs [[_ [HprojL _]] [Hσ _]]] |
                            [evt [[HprojL _] [_ Hτ]]]]]; simpl in *.
        + (* Sync case: projL evs = ɛ, but StLess only has transitions on
             events where projL is visible *)
          destruct evs as [evsm | evsp]; simpl in HprojL;
          [destruct evsm as [am bm | am | bm] | destruct evsp as [ap bp | ap | bp]];
          simpl in HprojL, Hσ; try discriminate; contradiction.
        + (* Left-only case: similar - evs must be asyncr but StLess has no such transitions *)
          destruct evs as [evs' | ]; simpl in Hσ; try contradiction.
          destruct evs' as [evsm | evsp]; simpl in HprojL;
          [destruct evsm as [am bm | am | bm] | destruct evsp as [ap bp | ap | bp]];
          simpl in HprojL, Hσ; try discriminate; contradiction.
        + (* Right-only case: similar for evt *)
          destruct evt as [evt' | ]; simpl in Hτ; try contradiction.
          destruct evt' as [evtm | evtp]; simpl in HprojL;
          [destruct evtm as [bm cm | bm | cm] | destruct evtp as [bp cp | bp | cp]];
          simpl in HprojL, Hτ; try discriminate; contradiction.
    Qed.

    (** Backward simulation helper *)
    Lemma StLess_compose_sim_backward {A B C : sig} (gen : Sig.m A B) (gen' : Sig.m B C) :
      forall (s : unit),
        alts_sim' (StLess (gen' @ gen)) (compose (StLess gen') (StLess gen) ) s (tt, tt).
    Proof.
      pcofix IH. intros [].
      pfold. split.
      - (* Visible transitions *)
        intros ev [] Htrans. simpl in Htrans.
        exists (tt, tt). split.
        + (* weak_trans on composed system *)
          apply compose_StLess_weak_trans. simpl.
          destruct ev as [evm | evp].
          * (* Negative polarity *)
            destruct evm as [am cm | am | cm]; simpl in Htrans; try contradiction.
            -- (* ev = neg ⟨am | cm⟩ : (gen' @ gen)^- am = 'cm *)
               unfold Sig.compose in Htrans. simpl in Htrans.
               unfold AsyncEventsBase.compose in Htrans.
               destruct (gen^- am) as [bm |] eqn:Hgen; simpl in Htrans.
               ++ (* gen^- am = 'bm, gen'^- bm = 'cm *)
                  left. exists (neg ⟨am | bm⟩), (neg ⟨bm | cm⟩).
                  simpl. repeat split; auto.
               ++ discriminate Htrans.
            -- (* ev = neg ⟨am |⟩ : (gen' @ gen)^- am = ɛ *)
               unfold Sig.compose in Htrans. simpl in Htrans.
               unfold AsyncEventsBase.compose in Htrans.
               destruct (gen^- am) as [bm |] eqn:Hgen; simpl in Htrans.
               ++ (* gen^- am = 'bm, gen'^- bm = ɛ *)
                  left. exists (neg ⟨am | bm⟩), (neg ⟨bm |⟩).
                  simpl. repeat split; auto.
               ++ (* gen^- am = ɛ *)
                  right. left. exists ('neg ⟨am |⟩).
                  simpl. repeat split; auto.
          * (* Positive polarity *)
            destruct evp as [ap cp | ap | cp]; simpl in Htrans; try contradiction.
            -- (* ev = pos ⟨ap | cp⟩ : (gen' @ gen)^+ ap = 'cp *)
               unfold Sig.compose in Htrans. simpl in Htrans.
               unfold AsyncEventsBase.compose in Htrans.
               destruct (gen^+ ap) as [bp |] eqn:Hgen; simpl in Htrans.
               ++ left. exists (pos ⟨ap | bp⟩), (pos ⟨bp | cp⟩).
                  simpl. repeat split; auto.
               ++ discriminate Htrans.
            -- (* ev = pos ⟨ap |⟩ : (gen' @ gen)^+ ap = ɛ *)
               unfold Sig.compose in Htrans. simpl in Htrans.
               unfold AsyncEventsBase.compose in Htrans.
               destruct (gen^+ ap) as [bp |] eqn:Hgen; simpl in Htrans.
               ++ left. exists (pos ⟨ap | bp⟩), (pos ⟨bp |⟩).
                  simpl. repeat split; auto.
               ++ right. left. exists ('pos ⟨ap |⟩).
                  simpl. repeat split; auto.
        + right. apply IH.
      - (* Tau transitions - StLess has none *)
        intros [] Htrans. simpl in Htrans. contradiction.
    Qed.
    
    Proposition StLess_compose {A B C : sig} {gen : Sig.m A B} {gen' : Sig.m B C} :
      compose (StLess gen') (StLess gen) ≈ StLess (gen' @ gen).
    Proof.
      split.
      (* Forward: compose (StLess gen) (StLess gen') ≲ StLess (gen' @ gen) *)
      - intros [s1 s2] [Hstart1 Hstart2].
        exists tt. split; [exact I |].
        apply StLess_compose_sim_forward.
      (* Backward: StLess (gen' @ gen) ≲ compose (StLess gen) (StLess gen') *)
      - intros s Hstart.
        exists (tt, tt). split; [split; exact I |].
        apply StLess_compose_sim_backward.
    Qed.

    Proposition id_StLess {A : sig} : id A ≈ StLess (Sig.id A).
    Proof.
      split. 
      - intros [] _. exists tt. split. exact I. 
        pcofix IH. pfold. split.
        + intros ev [] Hid.
          exists tt. split.
          * apply StLess_weak_trans. simpl.
            apply id_trans_iff in Hid.
            destruct Hid as [a [Heq Hproj]]. 
            injection Heq; clear Heq; intros Heq.
            rewrite <- Heq in Hproj; clear Heq.
            destruct ev as [[ev | ev | ev] | [ev | ev | ev]]; 
            try unfold AsyncEvents.id; simpl.
            all: unfold_proj in Hproj;
              inversion Hproj; subst; reflexivity.
          * right. apply IH.
        + intros [] Hid. simpl in Hid. contradiction.
      - intros [] _. exists tt. split. exact I.
        pcofix IH. pfold. split.
        + intros ev [] Hid. exists tt. split.
          * apply id_weak_trans. apply id_trans_iff.
            exists ev. split. reflexivity.
            simpl in Hid.
            destruct ev as [[ev | ev | ev] | [ev | ev | ev]];
            unfold AsyncEvents.id in Hid; simpl in Hid; unfold_proj;
            inversion Hid; reflexivity.
          * right. apply IH.
        + intros [] Hid. contradiction.
    Qed.

  End StateLess.

End OALTSBase.