Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Alts.
Require Import oalts.Sig.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid.
Require Import Morphisms.
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

  Section Compose_Aux.
    Lemma eps_star_compose_right {A B C : sig} (σ : oalts A B) (τ : oalts B C)
      (sσ : states σ) (s1τ s2τ : states τ) :
      eps_star τ s1τ s2τ -> eps_star (compose τ σ) (sσ, s1τ) (sσ, s2τ).
    Proof.
      induction 1 as [| s0 s1 s2 Hstep Hstar IH].
      - constructor.
      - eapply eps_step; [| exact IH].
        right. right. exists ɛ. simpl.
        repeat split; try reflexivity. exact Hstep.
    Qed.

    Lemma eps_star_compose_left {A B C : sig} (σ : oalts A B) (τ : oalts B C)
      (s1σ s2σ : states σ) (sτ : states τ) :
      eps_star σ s1σ s2σ -> eps_star (compose τ σ) (s1σ, sτ) (s2σ, sτ).
    Proof.
      induction 1 as [| s0 s1 s2 Hstep Hstar IH].
      - constructor.
      - eapply eps_step; [| exact IH].
        right. left. exists ɛ. simpl.
        repeat split; try reflexivity. exact Hstep.
    Qed.
    
  End Compose_Aux.

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
        apply eps_refl. exact Hid.
    Qed.

  End Id_Aux.

  Section Compose_Id_Left.

    Definition compose_id_rel {A B : sig} (σ : oalts A B) 
      (s1 : states (compose (id B) σ)) (s2 : states σ) : Prop :=
      eps_star σ s2 (fst s1) /\ snd s1 = tt.

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
        + (* weak_trans: σ matches via eps_star then visible *)
          exists s. split; [eapply eps_star_trans; [exact Hstar | constructor] |].
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
          eapply eps_star_trans; [exact Hstar | econstructor; [exact Hσ | constructor]].
        + (* Right-only: contradiction *)
          destruct Heqs as [HprojL [_ HprojR]]. simpl in *.
          destruct evt as [ev' |]; [exfalso; eapply projL_projR_eps; [symmetry; exact HprojL | exact HprojR] |].
          simpl in Hid. contradiction.
    Qed.

    Lemma compose_id_left_forward {A B} (σ : oalts A B) :
      forall s, (s, tt) ≲'[compose (id B) σ, σ] s.
    Proof.
      intros s.
      apply (alts_sim_coind (compose (id B) σ) σ (compose_id_rel σ) (compose_id_rel_sim σ)).
      split; [constructor | reflexivity].
    Qed.

    (** Relation for backward simulation: σ can be "ahead" via taus *)
    Definition compose_id_rel_back {A B : sig} (σ : oalts A B)
      (s1 : states σ) (s2 : states (compose (id B) σ)) : Prop :=
      eps_star σ (fst s2) s1 /\ snd s2 = tt.

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
        + (* weak_trans: compose does eps_star then visible *)
          exists (s1, tt). split.
          * (* eps_star from (s2, tt) to (s1, tt) by propagating σ's taus *)
            apply eps_star_compose_left. exact Hstar.
          * (* visible transition (s1, tt) --'ev--> (s1', tt) *)
            destruct (projR ev) as [b | ] eqn:HprojR.
            -- (* B component: sync with id *)
              left. exists ev.
              destruct b as [bm | bp].
              ++ exists (neg ⟨bm | bm⟩). simpl. repeat split; auto.
              ++ exists (pos ⟨bp | bp⟩). simpl. repeat split; auto.
            -- (* No B component: σ-only *)
              right. left. exists ('ev). simpl. repeat split; auto.
        + (* Relation preserved: eps_star σ s1' s1' *)
          split; [constructor | reflexivity].
      - (* Tau case: σ does s1 --ɛ--> s1' *)
        intros s1' Htrans.
        (* σ advances, compose stays, relation still holds by transitivity *)
        split; [| reflexivity].
        eapply eps_star_trans; [exact Hstar | econstructor; [exact Htrans | constructor]].
    Qed.

    Lemma compose_id_left_backward {A B : sig} (σ : oalts A B) :
      forall (s : states σ), s ≲'[σ, compose (id B) σ] (s, tt).
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
      eps_star σ s2 (snd s1) /\ fst s1 = tt.

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
        + (* weak_trans: σ matches via eps_star then visible *)
          exists s. split; [eapply eps_star_trans; [exact Hstar | constructor] |].
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
          eapply eps_star_trans; [exact Hstar | econstructor; [exact Hσ | constructor]].
    Qed.

    Lemma compose_id_right_forward {A B} (σ : oalts A B) :
      forall s, (tt, s) ≲'[compose σ (id A), σ] s.
    Proof.
      intros s.
      apply (alts_sim_coind (compose σ (id A)) σ (compose_id_rel_r σ) (compose_id_rel_r_sim σ)).
      split; [constructor | reflexivity].
    Qed.

    (** Relation for backward simulation: σ can be "ahead" via taus *)
    Definition compose_id_rel_r_back {A B : sig} (σ : oalts A B)
      (s1 : states σ) (s2 : states (compose σ (id A))) : Prop :=
      eps_star σ (snd s2) s1 /\ fst s2 = tt.

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
        + (* weak_trans: compose does eps_star then visible *)
          exists (tt, s1). split.
          * (* eps_star from (tt, s2) to (tt, s1) by propagating σ's taus *)
            apply eps_star_compose_right. exact Hstar.
          * (* visible transition (tt, s1) --'ev--> (tt, s1') *)
            destruct (projL ev) as [a | ] eqn:HprojL.
            -- (* A component: sync with id *)
               left.
               destruct a as [am | ap].
               ++ exists (neg ⟨am | am⟩), ev. simpl. repeat split; auto.
               ++ exists (pos ⟨ap | ap⟩), ev. simpl. repeat split; auto.
            -- (* No A component: σ-only *)
               right. right. exists ('ev). simpl. repeat split; auto.
        + (* Relation preserved: eps_star σ s1' s1' *)
          split; [constructor | reflexivity].
      - (* Tau case: σ does s1 --ɛ--> s1' *)
        intros s1' Htrans.
        (* σ advances, compose stays, relation still holds by transitivity *)
        split; [| reflexivity].
        eapply eps_star_trans; [exact Hstar | econstructor; [exact Htrans | constructor]].
    Qed.

    Lemma compose_id_right_backward {A B : sig} (σ : oalts A B) :
      forall (s : states σ), s ≲'[σ, compose σ (id A)] (tt, s).
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

  Section Compose_Mon_L.

    (* Helper: lift eps_star from τ' to compose τ' σ via right-only taus *)
    Definition compose_mon_l_rel {A B C : sig} {σ : oalts A B} {τ τ' : oalts B C}
      (s1 : states (compose τ σ)) (s2 : states (compose τ' σ)) : Prop :=
      exists s2' : states (compose τ' σ),
        eps_star (compose τ' σ) s2 s2' /\
        fst s1 = fst s2' /\
        (snd s1) ≲'[τ, τ'] (snd s2').

    Proposition compose_mon_l {A B C : sig} {σ : oalts A B} {τ τ' : oalts B C} :
      τ ≲ τ' -> compose τ σ ≲ compose τ' σ.
    Proof.
      intros Hsim. intros [sσ sτ] [Hstartσ Hstartτ].
      specialize (Hsim sτ Hstartτ). destruct Hsim as [sτ' [Hstartτ' Hsim]].
      exists (sσ, sτ'). split. split; assumption.
      apply (alts_sim_coind _ _ compose_mon_l_rel).
      - clear Hstartσ Hstartτ Hstartτ' sσ Hsim sτ sτ'.
        intros [sσ sτ] [sσ_c sτ'_c] [[sσ_s sτ'_s] [Hstar [Heqσ HR]]].
        simpl in Heqσ, HR. subst sσ_s.
        punfold HR. destruct HR as [Hvis Heps]. split.
        + (* Visible cases *)
          intros ev [s2σ s2τ] Htrans.
          destruct Htrans as [[evs [evt [Heqs [Hσ Hτ]]]] |
                             [[evs [Heqs [Hσ Hτ]]] | [evt [Heqs [Hσ Hτ]]]]].
          * (* Sync visible *)
            specialize (Hvis evt s2τ Hτ). destruct Hvis as [s2τ' [Hwtrans Hsim']].
            exists (s2σ, s2τ').
            destruct Hwtrans as [sτ'_mid [Hstar_τ' Htrans_τ']].
            split.
            -- exists (sσ, sτ'_mid). split.
               ++ eapply eps_star_trans; [exact Hstar |].
                  apply eps_star_compose_right. exact Hstar_τ'.
               ++ left. exists evs, evt. split; [exact Heqs |].
                  split; assumption.
            -- exists (s2σ, s2τ'). split; [constructor |].
               split; [reflexivity |]. simpl.
               destruct Hsim' as [Hsim' | []]; exact Hsim'.
          * (* Left-only visible *)
            simpl in Hτ. subst s2τ.
            exists (s2σ, sτ'_s).
            split.
            -- exists (sσ, sτ'_s). split; [exact Hstar |].
               right. left. exists evs. split; [exact Heqs |].
               split; [exact Hσ | reflexivity].
            -- exists (s2σ, sτ'_s). split; [constructor |].
               split; [reflexivity |]. simpl.
               pfold. split.
               ++ intros ev' s2' Htrans'. specialize (Hvis ev' s2' Htrans').
                  destruct Hvis as [s2'' [Hweak HR']].
                  exists s2''. split; [exact Hweak |].
                  destruct HR' as [HR' | []]; left; exact HR'.
               ++ intros s2' Htrans'. specialize (Heps s2' Htrans').
                  destruct Heps as [Heps' | []]; left; exact Heps'.
          * (* Right-only visible *)
            simpl in Hσ. subst s2σ.
            destruct evt as [evt' | ].
            -- specialize (Hvis evt' s2τ Hτ). destruct Hvis as [s2τ' [Hwtrans Hsim']].
               exists (sσ, s2τ').
               destruct Hwtrans as [sτ'_mid [Hstar_τ' Htrans_τ']].
               split.
               ++ exists (sσ, sτ'_mid). split.
                  ** eapply eps_star_trans; [exact Hstar |].
                     apply eps_star_compose_right. exact Hstar_τ'.
                  ** right. right. exists ('evt'). split; [exact Heqs |].
                     split; [reflexivity | exact Htrans_τ'].
               ++ exists (sσ, s2τ'). split; [constructor |].
                  split; [reflexivity |]. simpl.
                  destruct Hsim' as [Hsim' | []]; exact Hsim'.
            -- destruct Heqs as [_ [HprojL HprojR]]. simpl in HprojL, HprojR.
               exfalso. eapply projL_projR_eps; [symmetry; exact HprojL | symmetry; exact HprojR].
        + (* Tau cases *)
          intros [s2σ s2τ] Htrans.
          destruct Htrans as [[evs [evt [Heqs [Hσ Hτ]]]] |
                             [[evs [Heqs [Hσ Hτ]]] | [evt [Heqs [Hσ Hτ]]]]].
          * (* Sync tau: both σ and τ do visible steps that produce tau *)
            (* τ did visible 'evt, so we can use Hvis *)
            specialize (Hvis evt s2τ Hτ). destruct Hvis as [s2τ' [Hwtrans Hsim']].
            destruct Hwtrans as [sτ'_mid [Hstar_τ' Htrans_τ']].
            (* compose τ' σ can catch up: eps_star to (sσ, sτ'_mid), then sync tau *)
            exists (s2σ, s2τ'). split.
            -- eapply eps_star_trans; [exact Hstar |].
               eapply eps_star_trans.
               ++ (* Right-only taus for τ' catching up *)
                  apply eps_star_compose_right. exact Hstar_τ'.
               ++ (* Sync tau step *)
                  econstructor; [| constructor].
                  left. exists evs, evt. split; [exact Heqs |].
                  split; [exact Hσ | exact Htrans_τ'].
            -- split; [reflexivity |]. simpl.
               destruct Hsim' as [Hsim' | []]; exact Hsim'.
          * (* Left-only tau: σ does tau, τ stays *)
            simpl in Hτ. subst s2τ.
            exists (s2σ, sτ'_s). split.
            -- eapply eps_star_trans; [exact Hstar |].
               econstructor; [| constructor].
               right. left. exists evs. split; [exact Heqs |].
               split; [exact Hσ | reflexivity].
            -- split; [reflexivity |]. simpl.
               pfold. split.
               ++ intros ev' s2' Htrans'. specialize (Hvis ev' s2' Htrans').
                  destruct Hvis as [s2'' [Hweak HR']].
                  exists s2''. split; [exact Hweak |].
                  destruct HR' as [HR' | []]; left; exact HR'.
               ++ intros s2' Htrans'. specialize (Heps s2' Htrans').
                  destruct Heps as [Heps' | []]; left; exact Heps'.
          * (* Right-only tau: τ does tau, σ stays *)
            simpl in Hσ. symmetry in Hσ. subst s2σ.
            destruct Heqs as [HprojL [_ HprojR]]. simpl in HprojL, HprojR.
            destruct evt as [evt' |]; simpl in Hτ.
            -- (* evt' visible but projections are ε - contradiction *)
               destruct evt' as [evtm | evtp];
               [destruct evtm as [bm cm | bm | cm] | destruct evtp as [bp cp | bp | cp]];
               simpl in HprojL, HprojR; try discriminate.
            -- (* evt = ε, τ does tau *)
               specialize (Heps s2τ Hτ).
               exists (sσ, sτ'_s). split.
               ++ exact Hstar.
               ++ split; [reflexivity |]. simpl.
                  destruct Heps as [Heps' | []]; exact Heps'.
      - unfold compose_mon_l_rel.
        exists (sσ, sτ'). split; [constructor |].
        split; [reflexivity | exact Hsim].
    Qed.

  End Compose_Mon_L.

  Section Compose_Mon_R.

    (* Relation for right monotonicity: σ' can catch up via eps_star *)
    Definition compose_mon_r_rel {A B C : sig} {σ σ' : oalts A B} {τ : oalts B C}
      (s1 : states (compose τ σ)) (s2 : states (compose τ σ')) : Prop :=
      exists s2' : states (compose τ σ'),
        eps_star (compose τ σ') s2 s2' /\
        snd s1 = snd s2' /\
        (fst s1) ≲'[σ, σ'] (fst s2').

    Proposition compose_mon_r {A B C : sig} {σ σ' : oalts A B} {τ : oalts B C} :
      σ ≲ σ' -> compose τ σ ≲ compose τ σ'.
    Proof.
      intros Hsim. intros [sσ sτ] [Hstartσ Hstartτ].
      specialize (Hsim sσ Hstartσ). destruct Hsim as [sσ' [Hstartσ' Hsim]].
      exists (sσ', sτ). split. split; assumption.
      apply (alts_sim_coind _ _ compose_mon_r_rel).
      - clear Hstartσ Hstartτ Hstartσ' sτ Hsim sσ sσ'.
        intros [sσ sτ] [sσ'_c sτ_c] [[sσ'_s sτ_s] [Hstar [Heqτ HR]]].
        simpl in Heqτ, HR. subst sτ_s.
        punfold HR. destruct HR as [Hvis Heps]. split.
        + (* Visible cases *)
          intros ev [s2σ s2τ] Htrans.
          destruct Htrans as [[evs [evt [Heqs [Hσ Hτ]]]] |
                             [[evs [Heqs [Hσ Hτ]]] | [evt [Heqs [Hσ Hτ]]]]].
          * (* Sync visible: both σ and τ do visible steps *)
            specialize (Hvis evs s2σ Hσ). destruct Hvis as [s2σ' [Hwtrans Hsim']].
            exists (s2σ', s2τ).
            destruct Hwtrans as [sσ'_mid [Hstar_σ' Htrans_σ']].
            split.
            -- exists (sσ'_mid, sτ). split.
               ++ eapply eps_star_trans; [exact Hstar |].
                  apply eps_star_compose_left. exact Hstar_σ'.
               ++ left. exists evs, evt. split; [exact Heqs |].
                  split; assumption.
            -- exists (s2σ', s2τ). split; [constructor |].
               split; [reflexivity |]. simpl.
               destruct Hsim' as [Hsim' | []]; exact Hsim'.
          * (* Left-only visible: σ does visible step, τ stays *)
            simpl in Hτ. subst s2τ.
            destruct evs as [evs' | ].
            -- (* evs' visible *)
               specialize (Hvis evs' s2σ Hσ). destruct Hvis as [s2σ' [Hwtrans Hsim']].
               exists (s2σ', sτ).
               destruct Hwtrans as [sσ'_mid [Hstar_σ' Htrans_σ']].
               split.
               ++ exists (sσ'_mid, sτ). split.
                  ** eapply eps_star_trans; [exact Hstar |].
                     apply eps_star_compose_left. exact Hstar_σ'.
                  ** right. left. exists ('evs'). split; [exact Heqs |].
                     split; [exact Htrans_σ' | reflexivity].
               ++ exists (s2σ', sτ). split; [constructor |].
                  split; [reflexivity |]. simpl.
                  destruct Hsim' as [Hsim' | []]; exact Hsim'.
            -- (* evs = ε - contradiction since this produces visible ev *)
               destruct Heqs as [_ [HprojL HprojR]]. simpl in HprojL, HprojR.
               exfalso. eapply projL_projR_eps; [symmetry; exact HprojL | symmetry; exact HprojR].
          * (* Right-only visible: τ does visible step, σ stays *)
            simpl in Hσ. subst s2σ.
            destruct evt as [evt' | ].
            -- exists (sσ'_s, s2τ).
               split.
               ++ exists (sσ'_s, sτ). split; [exact Hstar |].
                  right. right. exists ('evt'). split; [exact Heqs |].
                  split; [reflexivity | exact Hτ].
               ++ exists (sσ'_s, s2τ). split; [constructor |].
                  split; [reflexivity |]. simpl.
                  pfold. split.
                  ** intros ev' s2' Htrans'. specialize (Hvis ev' s2' Htrans').
                     destruct Hvis as [s2'' [Hweak HR']].
                     exists s2''. split; [exact Hweak |].
                     destruct HR' as [HR' | []]; left; exact HR'.
                  ** intros s2' Htrans'. specialize (Heps s2' Htrans').
                     destruct Heps as [Heps' | []]; left; exact Heps'.
            -- destruct Heqs as [_ [HprojL HprojR]]. simpl in HprojL, HprojR.
               exfalso. eapply projL_projR_eps; [symmetry; exact HprojL | symmetry; exact HprojR].
        + (* Tau cases *)
          intros [s2σ s2τ] Htrans.
          destruct Htrans as [[evs [evt [Heqs [Hσ Hτ]]]] |
                             [[evs [Heqs [Hσ Hτ]]] | [evt [Heqs [Hσ Hτ]]]]].
          * (* Sync tau: both σ and τ do visible steps that produce tau *)
            specialize (Hvis evs s2σ Hσ). destruct Hvis as [s2σ' [Hwtrans Hsim']].
            destruct Hwtrans as [sσ'_mid [Hstar_σ' Htrans_σ']].
            exists (s2σ', s2τ). split.
            -- eapply eps_star_trans; [exact Hstar |].
               eapply eps_star_trans.
               ++ apply eps_star_compose_left. exact Hstar_σ'.
               ++ econstructor; [| constructor].
                  left. exists evs, evt. split; [exact Heqs |].
                  split; [exact Htrans_σ' | exact Hτ].
            -- split; [reflexivity |]. simpl.
               destruct Hsim' as [Hsim' | []]; exact Hsim'.
          * (* Left-only tau: σ does tau, τ stays *)
            simpl in Hτ. subst s2τ.
            destruct evs as [evs' |]; simpl in Hσ.
            -- (* evs' visible but projections are ε - contradiction *)
               destruct Heqs as [HprojR [HprojL _]]. simpl in HprojL, HprojR.
               destruct evs' as [evsm | evsp];
               [destruct evsm as [am bm | am | bm] | destruct evsp as [ap bp | ap | bp]];
               simpl in HprojL, HprojR; try discriminate.
            -- (* evs = ε, σ does tau *)
               specialize (Heps s2σ Hσ).
               exists (sσ'_s, sτ). split.
               ++ exact Hstar.
               ++ split; [reflexivity |]. simpl.
                  destruct Heps as [Heps' | []]; exact Heps'.
          * (* Right-only tau: τ does tau, σ stays *)
            simpl in Hσ. symmetry in Hσ. subst s2σ.
            exists (sσ'_s, s2τ). split.
            -- eapply eps_star_trans; [exact Hstar |].
               econstructor; [| constructor].
               right. right. exists evt. split; [exact Heqs |].
               split; [reflexivity | exact Hτ].
            -- split; [reflexivity |]. simpl.
               pfold. split.
               ++ intros ev' s2' Htrans'. specialize (Hvis ev' s2' Htrans').
                  destruct Hvis as [s2'' [Hweak HR']].
                  exists s2''. split; [exact Hweak |].
                  destruct HR' as [HR' | []]; left; exact HR'.
               ++ intros s2' Htrans'. specialize (Heps s2' Htrans').
                  destruct Heps as [Heps' | []]; left; exact Heps'.
      - unfold compose_mon_r_rel.
        exists (sσ', sτ). split; [constructor |].
        split; [reflexivity | exact Hsim].
    Qed.

  End Compose_Mon_R.

  Section Compose_Mon.

    Proposition compose_mon {A B C : sig} {σ σ' : oalts A B} {τ τ' : oalts B C} :
      σ ≲ σ' -> τ ≲ τ' -> compose τ σ ≲ compose τ' σ'.
    Proof.
      intros H H'. pose (compose_mon_r (τ := τ) H) as HR.
      pose (compose_mon_l (σ := σ') H') as HL.
      eapply alts_sim_trans. exact HR. exact HL.
    Qed.

    Proposition compose_cong_l {A B C : sig} {σ : oalts A B} {τ τ' : oalts B C} :
      τ ≈ τ' -> compose τ σ ≈ compose τ' σ.
    Proof.
      intros H. destruct H as [Hfw Hbw].
      split; apply compose_mon_l; assumption.
    Qed.

    Proposition compose_cong_r {A B C : sig} {σ σ' : oalts A B} {τ : oalts B C} :
      σ ≈ σ' -> compose τ σ ≈ compose τ σ'.
    Proof.
      intros H. destruct H as [Hfw Hbw].
      split; apply compose_mon_r; assumption.
    Qed.

    Proposition compose_cong {A B C : sig} {σ σ' : oalts A B} {τ τ' : oalts B C} :
      σ ≈ σ' -> τ ≈ τ' -> compose τ σ ≈ compose τ' σ'.
    Proof.
      intros H H'. pose (compose_cong_r (τ := τ) H) as HR.
      pose (compose_cong_l (σ := σ') H') as HL.
      eapply alts_bisim_trans. exact HR. exact HL.
    Qed.

  End Compose_Mon.

End OALTSBase.

Module OALTS.
  Export AsyncEvents.
  Export Sig.
  Export ALTS.
  Export Setoid Morphisms.
  Include OALTSBase.

  Add Parametric Relation {A : Type} : (alts A) alts_bisim
    reflexivity proved by alts_bisim_refl
    symmetry proved by alts_bisim_sym
    transitivity proved by alts_bisim_trans
    as alts_bisim_equiv.

  Add Parametric Morphism {A B C : sig} : (@compose A B C)
    with signature alts_bisim ==> alts_bisim ==> alts_bisim
    as compose_morphism.
  Proof.
    intros τ τ' Hτ σ σ' Hσ.
    apply compose_cong; assumption.
  Qed.

  Module StateLess. (* <: Functor Sig OALTSBase *)
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
        s ≲'[compose (StLess gen') (StLess gen), StLess (gen' @ gen)] tt.
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
        s ≲'[StLess (gen' @ gen), compose (StLess gen') (StLess gen)] (tt, tt).
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

  Bind Scope oalts_scope with oalts.
  Delimit Scope oalts_scope with oalts.

  Notation "τ @ σ" := (compose τ σ) (at level 45, right associativity) : oalts_scope.
  Notation "σ ;; τ" := (compose τ σ) (at level 60, right associativity) : oalts_scope.

  Open Scope oalts_scope.

End OALTS.
