Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Alts.
Require Import oalts.Sig.
Require Import Coq.Logic.FunctionalExtensionality.
From Paco Require Import paco.

Module OALTS. (* <: Category. *)
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
        | '(neg ⟨an | bn⟩) => an = bn
        | '(pos ⟨ap | bp⟩) => ap = bp
        | _ => False
        end
    |}.

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
      simpl in Heq;
      try unfold AsyncEvents.Plus.i1, AsyncEvents.Plus.i2, 
        AsyncEvents.Prod.p1, AsyncEvents.Prod.p2, AsyncEvents.compose in Heq;
      inversion Heq; reflexivity.
  Qed.

  Section Compose_Id_Left.
    (** Define the relation explicitly *)
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

  (* Module StLess.
    Open Scope event_obj_scope.

    Definition StLess {A B : sig} (gen : Sig.m A B) : oalts A B :=
      {|
        states := unit;
        start := fun _ => True;
        trans := fun _ ev _ =>
          match ev with
          | '⟨src ap | tgt bp⟩ => gen^+ ap = 'bp
          | '⟨tgt bm | src am⟩ => gen^- am = 'bm
          | '⟨src ap |⟩ => gen^+ ap = ɛ
          | '⟨| src am⟩ => gen^- am = ɛ
          | _ => False
          end
      |}.

    (** Helper: weak_trans on StLess reduces to trans (states are trivial) *)
    Lemma StLess_weak_trans {A B : sig} (gen : Sig.m A B) (s : unit) (ev : «A -o B») (s' : unit) :
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
    Lemma compose_StLess_weak_trans {A B C : sig} (gen : Sig.m A B) (gen' : Sig.m B C)
        (s : unit * unit) (ev : «A -o C») (s' : unit * unit) :
      weak_trans (compose (StLess gen') (StLess gen)) s ev s' <->
      trans (compose(StLess gen') (StLess gen)) s ('ev) s'.
    Proof.
      split.
      - intros [s'' [Hstar Htrans]].
        (* All unit*unit values are equal, so s = s'' = s' *)
        destruct s as [u1 u2], s'' as [v1 v2], s' as [w1 w2].
        destruct u1, u2, v1, v2, w1, w2.
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
      pcofix IH. intros [s1 s2].
      pfold. split.
      + (* Visible transitions *)
        intros ev [t1 t2] Htrans. simpl in Htrans.
        exists tt. split.
        * (* weak_trans on RHS *)
          apply StLess_weak_trans. simpl.
          (* Analyze the three cases from compose *)
          destruct Htrans as [Hsync | [Hleft | Hright]].
          -- (* Sync case: both σ and τ make visible transitions *)
             destruct Hsync as [evs [evt [[Hmatch [HprojL HprojR]] [Hσ Hτ]]]].
             simpl in Hσ, Hτ.
             (* Case analysis on evs pattern in StLess gen *)
             destruct evs as [[ap' | bm'] [am' | bp'] | [ap' | bm'] | [am' | bp']];
             simpl in Hσ; try contradiction;
             simpl in Hmatch;
             destruct evt as [[bp'' | cm'] [bm'' | cp'] | [bp'' | cm'] | [bm'' | cp']];
             simpl in Hτ, Hmatch; try discriminate; try contradiction;
             simpl in HprojL, HprojR;
             destruct ev as [[ap | cm] [am | cp] | [ap | cm] | [am | cp]];
             simpl in HprojL, HprojR; try discriminate;
             inversion Hmatch; subst; inversion HprojL; subst;
             try (inversion HprojR; subst);
             simpl;
             unfold Sig.compose; simpl;
             unfold AsyncEventsBase.compose;
             try (rewrite Hσ; exact Hτ);
             try (rewrite Hσ; reflexivity).
          -- (* Left-only case: only σ makes a transition, τ stays *)
             destruct Hleft as [evs [[HprojRɛ [HprojL HprojRev]] [Hσ Heq]]].
             destruct evs as [[ap' | bm'] [am' | bp'] | [ap' | bm'] | [am' | bp']];
             simpl in HprojRɛ; try discriminate;
             simpl in Hσ; try contradiction;
             simpl in HprojL, HprojRev;
             destruct ev as [[ap | cm] [am | cp] | [ap | cm] | [am | cp]];
             simpl in HprojL, HprojRev; try discriminate;
             inversion HprojL; subst;
             simpl;
             unfold Sig.compose; simpl;
             unfold AsyncEventsBase.compose;
             rewrite Hσ; reflexivity.
          -- (* Right-only case: only τ makes a transition, σ stays *)
             (* For right-only, projL evt = ɛ, but StLess gen' only has transitions
                where projL evt ≠ ɛ (⟨src bp | tgt cp⟩, ⟨tgt cm | src bm⟩, ⟨src bp |⟩, ⟨| src bm⟩)
                So this case is impossible. *)
             destruct Hright as [evt [[HprojLɛ [HprojLev HprojR]] [Heq Hτ]]].
             destruct evt as [[bp' | cm'] [bm' | cp'] | [bp' | cm'] | [bm' | cp']];
             simpl in Hτ, HprojLɛ; try discriminate; try destruct Hτ.
        * right. destruct t1, t2. apply IH.
      + (* Tau transitions - compose has no tau transitions that change state *)
        intros [t1 t2] Htrans.
        simpl in Htrans.
        (* Tau in compose means ev = ɛ, which has ext projL ɛ = ɛ and ext projR ɛ = ɛ *)
        (* The three disjuncts all require visible transitions in σ or τ *)
        (* But for ev = ɛ, we need to check what compose allows *)
        (* Actually looking at compose definition, trans takes Async E, so ɛ is valid *)
        (* For ɛ case: ext projL ɛ = ɛ and ext projR ɛ = ɛ *)
        (* All three cases require visible evs or evt which can't match ɛ constraints *)
        right. destruct t1, t2. apply IH.
    Qed.

    (** Backward simulation helper *)
    Lemma StLess_compose_sim_backward {A B C : sig} (gen : Sig.m A B) (gen' : Sig.m B C) :
      forall (s : unit),
        alts_sim' (StLess (gen' @ gen)) (compose (StLess gen') (StLess gen) ) s (tt, tt).
    Proof.
      pcofix IH. intros s.
      pfold. split.
      + (* Visible transitions *)
        intros ev t Htrans. simpl in Htrans.
        exists (tt, tt). split.
        * (* weak_trans on composed system - need to construct witness *)
          apply compose_StLess_weak_trans. simpl.
          (* Case analysis on ev *)
          destruct ev as [[ap | cm] [am | cp] | [ap | cm] | [am | cp]];
          simpl in Htrans; try contradiction.
          -- (* ev = ⟨src ap | tgt cp⟩ : (gen' @ gen)^+ ap = 'cp *)
             (* Compose (gen'^+) (gen^+) ap = 'cp means gen^+ ap = 'bp and gen'^+ bp = 'cp for some bp *)
             unfold Sig.compose in Htrans. simpl in Htrans.
             unfold AsyncEventsBase.compose in Htrans.
             destruct (gen^+ ap) as [bp |] eqn:Hgen; simpl in Htrans.
             ++ (* gen^+ ap = 'bp, gen'^+ bp = 'cp *)
                left. (* sync case *)
                exists ⟨src ap | tgt bp⟩, ⟨src bp | tgt cp⟩.
                simpl. repeat split; auto.
             ++ (* gen^+ ap = ɛ, but then Htrans says ɛ = 'cp - contradiction *)
                discriminate Htrans.
          -- (* ev = ⟨tgt cm | src am⟩ : (gen' @ gen)^- am = 'cm *)
             unfold Sig.compose in Htrans. simpl in Htrans.
             unfold AsyncEventsBase.compose in Htrans.
             destruct (gen^- am) as [bm |] eqn:Hgen; simpl in Htrans.
             ++ (* gen^- am = 'bm, gen'^- bm = 'cm *)
                left. (* sync case *)
                exists ⟨tgt bm | src am⟩, ⟨tgt cm | src bm⟩.
                simpl. repeat split; auto.
             ++ discriminate Htrans.
          -- (* ev = ⟨src ap |⟩ : (gen' @ gen)^+ ap = ɛ *)
             unfold Sig.compose in Htrans. simpl in Htrans.
             unfold AsyncEventsBase.compose in Htrans.
             destruct (gen^+ ap) as [bp |] eqn:Hgen; simpl in Htrans.
             ++ (* gen^+ ap = 'bp, gen'^+ bp = ɛ *)
                left. (* sync case with async evt *)
                exists ⟨src ap | tgt bp⟩, ⟨src bp |⟩.
                simpl. repeat split; auto.
             ++ (* gen^+ ap = ɛ *)
                right. left. (* left-only case *)
                exists ⟨src ap |⟩.
                simpl. repeat split; auto.
          -- (* ev = ⟨| src am⟩ : (gen' @ gen)^- am = ɛ *)
             unfold Sig.compose in Htrans. simpl in Htrans.
             unfold AsyncEventsBase.compose in Htrans.
             destruct (gen^- am) as [bm |] eqn:Hgen; simpl in Htrans.
             ++ (* gen^- am = 'bm, gen'^- bm = ɛ *)
                left. (* sync case with async evt *)
                exists ⟨tgt bm | src am⟩, ⟨| src bm⟩.
                simpl. repeat split; auto.
             ++ (* gen^- am = ɛ *)
                right. left. (* left-only case *)
                exists ⟨| src am⟩.
                simpl. repeat split; auto.
        * right. destruct t. apply IH.
      + (* Tau transitions *)
        intros t Htrans.
        simpl in Htrans. contradiction.
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
    
  End StLess. *)

End OALTS.