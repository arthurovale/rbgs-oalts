Require Import interfaces.Category.
Require Import oalts.AsyncEvents.
Require Import oalts.Sig.
Require Import oalts.PTree.

Module ALTS. (* <: Category. *)
  Import Sig.
  Import PTree.

  Record ALTS {A : sig} := {
    states : Type;
    trans_neg : states -> A^- -> states -> Prop;
    trans_pos : states -> A^+ -> states -> Prop;
    trans_tau : states -> states -> Prop;
  }.
  Arguments ALTS : clear implicits.

  Section Beh.
    Context {A : sig}.
    Variable σ : ALTS A.

    CoFixpoint beh (s : states σ) : ptree A :=
      go (
        StepF
          (neg_X := neg_step s)
          (pos_X := pos_step s)
          (fun x => fst (proj1_sig x))      (* neg_label *)
          (fun x => beh (snd (proj1_sig x))) (* neg_k *)
          (fun x => fst (proj1_sig x))      (* pos_label *)
          (fun x => beh (snd (proj1_sig x))) (* pos_k *)
      ).
  End Beh.
End ALTS.