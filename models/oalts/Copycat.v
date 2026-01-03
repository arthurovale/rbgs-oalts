Require Import Oalts.
Require Import Karoubi.

Import OALTS.

Require Import List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Open Scope event_obj_scope.

Definition cc_state {A : sig} : Type := list [A].

Definition cc_start {A : sig} (s : @cc_state A) : Prop := s = [].

Inductive cc_trans {A : sig} : 
  @cc_state A -> Async [A -o A]%event_obj -> @cc_state A -> Prop :=
| cc_recv_neg : forall s an, 
    cc_trans s ('neg ⟨ | an ⟩) ((neg an)::s)
| cc_send_neg : forall s1 s2 an,
    cc_trans (s1 ++ [neg an] ++ s2) ('neg ⟨ an | ⟩) (s1 ++ s2)
| cc_recv_pos : forall s ap,
    cc_trans s ('pos ⟨ ap | ⟩) ((pos ap)::s)
| cc_send_pos : forall s1 s2 ap,
    cc_trans (s1 ++ [pos ap] ++ s2) ('pos ⟨ | ap ⟩) (s1 ++ s2).

Definition cc (A : sig) : oalts A A :=
  {|
    states := @cc_state A;
    start := cc_start;
    trans := cc_trans;
  |}.

Lemma cc_no_eps {A : sig} : forall s s', ~ cc A s ɛ s'.
Proof.
  intros s s' H. inversion H.
Qed.

Lemma cc_eps_star_refl {A : sig} : forall s s', 
  eps_star (cc A) s s' -> s = s'.
Proof.
  intros s s' H. induction H.
  - reflexivity.
  - exfalso. exact (cc_no_eps _ _ H).
Qed.

Lemma cc_weak_trans {A : sig} (s : @cc_state A) (ev : [A -o A]%event_obj) 
  (s' : @cc_state A) : weak_trans (cc A) s ev s' <-> trans (cc A) s ('ev) s'.
Proof.
  split.
  - intros [s'' [Hstar Htrans]].
    apply cc_eps_star_refl in Hstar. subst. exact Htrans.
  - intros Htrans.
    exists s. split; [constructor | exact Htrans].
Qed.

Section Idempotence.

  Definition cc_idem_rel {A : sig} 
    (sc : @cc_state A * @cc_state A) (s : @cc_state A) : Prop :=
    exists sc', 
      eps_star (compose (cc A) (cc A)) sc sc' /\
      Permutation (fst sc' ++ snd sc') s.

  Lemma eps_star_cc_perm {A : sig} : forall s_l s_r s_l' s_r',
    eps_star (cc A ;; cc A) (s_l, s_r) (s_l', s_r') ->
    Permutation (s_l ++ s_r) (s_l' ++ s_r').
  Proof.
    intros s_l s_r s_l' s_r' H.
    remember (s_l, s_r) as s. remember (s_l', s_r') as s'.
    revert s_l s_r s_l' s_r' Heqs Heqs'.
    induction H as [s | s s'' s' Hstep Hstar IH]; intros; subst.
    - (* eps_refl *) injection Heqs' as -> ->. reflexivity.
    - (* eps_step *)
      destruct s'' as [s_l'' s_r''].
      transitivity (s_l'' ++ s_r''); [| apply IH; reflexivity].
      (* Analyze tau step *)
      clear IH Hstar.
      destruct_compose_trans Hstep.
      + (* Sync: internal communication *)
        inversion Hσ; inversion Hτ; subst;
        simpl in Heq_int, HprojL, HprojR; try discriminate.
        * (* cc_recv_neg + cc_send_neg: neg an moves from s_r to s_l *)
          inversion Heq_int; subst.
          simpl in H0, H2, H3; subst. rewrite app_assoc at 1.
          symmetry. simpl. rewrite app_assoc. apply Permutation_middle.
        * (* cc_send_pos + cc_recv_pos: pos ap moves from s_l to s_r *)
          inversion Heq_int; subst.
          simpl in H, H0, H3; subst. simpl.
          rewrite <- !app_assoc.
          apply Permutation_app_head. apply Permutation_middle.
      + (* Left-only: cc has no eps *)
        destruct evs as [evs' |]; simpl in Hσ.
        * simpl in Heq_int, HprojL, HprojR.
          destruct_lolli_event evs'; simpl in *; try discriminate; 
          inversion Hσ.
        * exfalso. apply (cc_no_eps _ _ Hσ).
      + (* Right-only: cc has no eps *)
        destruct evt as [evt' |]; simpl in Hτ.
        * simpl in Heq_int, HprojL, HprojR.
          destruct_lolli_event evt'; simpl in *; try discriminate;
          inversion Hτ.
        * exfalso. apply (cc_no_eps _ _ Hτ).
  Qed.

  Proposition cc_idem_fw {A : sig} : 
    forall sc1 s1, cc_idem_rel sc1 s1 -> 
      alts_simF (cc A ;; cc A) (cc A) cc_idem_rel sc1 s1.
  Proof.
  intros [s_l s_r] s1 [[s_l' s_r'] [Heps Hperm]]. simpl in *.
  split.
  - (* Visible: cc;;cc does visible, cc must match *)
    intros ev [s_l2 s_r2] Htrans.
    destruct_compose_trans Htrans.
    + (* Sync: both copycats do visible - internal communication *)
      (* This produces an external event, need to match with cc *)
      (* The permutation shifts elements between s_l' and s_r' *)
      inversion Hσ; inversion Hτ; unfold_proj in Heq_int;
      simpl in Heq_int, HprojL, HprojR; subst; inversion Heq_int; subst;
      try contradiction.
      all: (exfalso;
      eapply projL_projR_eps; 
      [symmetry; exact HprojL | symmetry; exact HprojR]).
    + (* Left-only: first cc does visible, second stays *)
      destruct evs as [evs' |]; [| exfalso; apply (cc_no_eps _ _ Hσ)].
      (* First cc does external move on left interface *)
      inversion Hσ; subst; simpl in Heq_int, HprojL, HprojR;
      try discriminate.
      * simpl in Hσ, Hτ, H, H0; subst.
        assert (Hperm_total : Permutation ((s0 ++ neg an :: s2) ++ s_r2) s1).
        { etransitivity; [apply eps_star_cc_perm; exact Heps | exact Hperm]. }
        assert (Hin : In (neg an) s1).
        { apply Permutation_in with ((s0 ++ neg an :: s2) ++ s_r2).
          - exact Hperm_total.
          - apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
        apply in_split in Hin as [l1 [l2 Hsplit]].
        exists (l1 ++ l2); split.
        -- apply cc_weak_trans. 
           assert (Hev : ev = neg ⟨ an | ⟩).
           { apply projL_ProjR_eq; symmetry. apply HprojL. apply HprojR. }
           subst ev. rewrite Hsplit. constructor.
        -- exists (s0 ++ s2, s_r2); split; [constructor | ].
           simpl. rewrite Hsplit in Hperm_total.
           rewrite <- app_assoc in Hperm_total. simpl in Hperm_total.
           rewrite <- app_assoc.
           apply Permutation_cons_app_inv with (a := neg an).
           etransitivity. 
           apply Permutation_cons_app. reflexivity.
           exact Hperm_total.
      * exists ((pos ap) :: s1). split.
        -- apply cc_weak_trans.
           assert (ev = pos ⟨ ap | ⟩).
           {
             apply projL_ProjR_eq; symmetry;
             assumption.
           } rewrite H. constructor.
        -- exists (s_l2, s_r2); split; [constructor | ].
           simpl in Hτ, H0; subst; simpl. rewrite <- Hperm.
           apply eps_star_cc_perm in Heps. rewrite <- Heps. reflexivity.
    + (* Right-only: second cc does visible, first stays *)
      destruct evt as [evt' |]; [| exfalso; apply (cc_no_eps _ _ Hτ)].
      inversion Hτ; subst; simpl in Heq_int, HprojL, HprojR;
      try discriminate.
      * (* cc_recv_neg: receives neg from external right *)
        simpl in Hσ, H0; subst.
        exists ((neg an) :: s1). split.
        -- apply cc_weak_trans.
          assert (Hev : ev = neg ⟨ | an ⟩).
          { apply projL_ProjR_eq; symmetry; [exact HprojL | exact HprojR]. }
          subst ev. constructor.
        -- exists (s_l2, (neg an) :: s_r); split; [constructor |].
          simpl. rewrite <- Hperm.
          apply eps_star_cc_perm in Heps. rewrite <- Heps. symmetry.
          apply Permutation_middle.
      * (* cc_send_pos: sends pos to external right - symmetric to cc_send_neg on left *)
        simpl in Hσ, Hτ, H, H0; subst.
        assert (Hperm_total : Permutation (s_l2 ++ (s0 ++ pos ap :: s2)) s1).
        { etransitivity; [apply eps_star_cc_perm; exact Heps | exact Hperm]. }
        assert (Hin : In (pos ap) s1).
        { apply Permutation_in with (s_l2 ++ s0 ++ pos ap :: s2).
          - exact Hperm_total.
          - apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
        apply in_split in Hin as [l1 [l2 Hsplit]].
        exists (l1 ++ l2); split.
        -- apply cc_weak_trans.
          assert (Hev : ev = pos ⟨ | ap ⟩).
          { apply projL_ProjR_eq; symmetry; [exact HprojL | exact HprojR]. }
          subst ev. rewrite Hsplit. constructor.
        -- exists (s_l2, s0 ++ s2); split; [constructor |].
          simpl. rewrite Hsplit in Hperm_total.
          rewrite app_assoc in Hperm_total.
          apply Permutation_cons_app_inv with (a := pos ap).
          etransitivity; [| exact Hperm_total].
          apply Permutation_cons_app. rewrite app_assoc. reflexivity.
  - (* Tau: cc;;cc does epsilon, relation preserved *)
    intros [s_l2 s_r2] Htrans.
    destruct_compose_trans Htrans; simpl in Hσ, Hτ.
    + (* Sync producing tau: internal communication that cancels *)
      (* Permutation preserved: move from one list to other *)
      inversion Hσ; inversion Hτ; subst;
      simpl in Heq_int, HprojL, HprojR; try discriminate.
      * (* cc_recv_neg + cc_send_neg: neg moves from right to left *)
        inversion Heq_int; subst.
        exists (neg an0 :: s_l, s0 ++ s2). split; [constructor |].
        simpl.
        assert (Hperm_base : Permutation (s_l ++ (s0 ++ [neg an0] ++ s2)) (s_l' ++ s_r')).
        { apply eps_star_cc_perm. exact Heps. }
        simpl in Hperm_base.
        etransitivity; [| exact Hperm].
        etransitivity; [| exact Hperm_base].
        rewrite app_assoc. simpl. rewrite app_assoc.
        apply Permutation_middle.
      * (* cc_send_pos + cc_recv_pos: pos moves from left to right *)
        inversion Heq_int; subst.
        exists (s0 ++ s2, pos ap0 :: s_r). split; [constructor |].
        simpl.
        assert (Hperm_base : Permutation ((s0 ++ [pos ap0] ++ s2) ++ s_r) (s_l' ++ s_r')).
        { apply eps_star_cc_perm. exact Heps. }
        etransitivity; [| exact Hperm].
        etransitivity; [| exact Hperm_base]. simpl.
        rewrite <- !app_assoc. apply Permutation_app_head. 
        symmetry. apply Permutation_middle.
    + (* Left-only tau: impossible since cc has no eps *)
      destruct evs as [evs' |]; simpl in Hσ.
      * exfalso. apply (projL_projR_eps (ev :=  evs'));
        assumption.
      * exfalso. apply (cc_no_eps _ _ Hσ).
    + (* Right-only tau: impossible since cc has no eps *)
      destruct evt as [evt' |]; simpl in Hτ.
      * exfalso. apply (projL_projR_eps (ev :=  evt')); [symmetry | ];
        assumption.
      * exfalso. apply (cc_no_eps _ _ Hτ).
  Qed.

Proposition cc_idempotence {A : sig} : cc A ;; cc A ≈ cc A.
Proof.
  split.
  - intros [s_l s_r] [Hstart_l Hstart_r].
    simpl in Hstart_l, Hstart_r. unfold cc_start in Hstart_l, Hstart_r. subst.
    exists []. split; [reflexivity |].
    apply (alts_sim_coind (cc A ;; cc A) (cc A) cc_idem_rel cc_idem_fw).
    exists ([], []). split; [constructor |]. simpl. reflexivity.
  - admit.
Admitted.
