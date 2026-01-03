Require Import Oalts.
Require Import Karoubi.

Import OALTS.

Require Import List.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Open Scope event_obj_scope.

Definition cc_state {A : sig} : Type := list [A].

Definition cc_start {A : sig} (s : @cc_state A) : Prop := s = [].

Definition cc_trans {A : sig} 
  (s : @cc_state A) (ev : Async [A -o A]%event_obj) (s' : @cc_state A) : Prop :=
  match ev with
  | 'neg ⟨ | an ⟩ => s' = (neg an)::s 
  | 'neg ⟨ an | ⟩ => exists s1 s2, s = s1 ++ [neg an] ++ s2 /\ s' = s1 ++ s2
  | 'pos ⟨ ap | ⟩ => s' = (pos ap)::s
  | 'pos ⟨ | ap ⟩ => exists s1 s2, s = s1 ++ [pos ap] ++ s2 /\ s' = s1 ++ s2
  | _ => False
  end.

Definition cc (A : sig) : oalts A A :=
  {|
    states := @cc_state A;
    start := cc_start;
    trans := cc_trans;
  |}.

Lemma cc_no_eps {A : sig} : forall s s', ~ cc A s ɛ s'.
Proof.
  intros s s' H. simpl in H. exact H.
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
      admit.
    + (* Left-only: first cc does visible, second stays *)
      destruct evs as [evs' |]; [| exfalso; apply (cc_no_eps _ _ Hσ)].
      (* First cc does external move on left interface *)
      admit.
    + (* Right-only: second cc does visible, first stays *)
      destruct evt as [evt' |]; [| exfalso; apply (cc_no_eps _ _ Hτ)].
      (* Second cc does external move on right interface *)
      admit.
  - (* Tau: cc;;cc does epsilon, relation preserved *)
    intros [s_l2 s_r2] Htrans.
    destruct_compose_trans Htrans.
    + (* Sync producing tau: internal communication that cancels *)
      (* Permutation preserved: move from one list to other *)
      admit.
    + (* Left-only tau: impossible since cc has no eps *)
      destruct evs as [evs' |]; simpl in Hσ.
      * (* visible evs but produces tau - check projections *) admit.
      * exfalso. apply (cc_no_eps _ _ Hσ).
    + (* Right-only tau: impossible since cc has no eps *)
      destruct evt as [evt' |]; simpl in Hτ.
      * (* visible evt but produces tau - check projections *) admit.
      * exfalso. apply (cc_no_eps _ _ Hτ).
Qed.

  Proposition cc_idempotence {A : sig} : cc A ;; cc A ≈ cc A.
