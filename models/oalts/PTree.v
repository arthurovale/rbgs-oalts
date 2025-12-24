Require Import oalts.AsyncEvents.
Require Import oalts.Sig.

Import Sig.

Module PTree. (* <: Category. *) 

  Variant ptreeF (A : sig) (ptree : Type) : Type :=
  (* blocked, waiting for something to happen *)
  (* should correspond to no enabled positive transition *)
  | BlockF
  (* system is done running *)
  (* should correspond to no enabled negative transition *)
  | DoneF
  (* step *)
  | StepF {neg_X pos_X : Type} 
    (neg_label : neg_X -> A^-) (neg_k : neg_X -> ptree)
    (pos_label : pos_X -> A^+) (pos_k : pos_X -> ptree)
  (* silent step, for productivity *)
  | GuardF (t : ptree).

  CoInductive ptree (A : sig) : Type :=
    go { _observe : ptreeF A (ptree A) }.

  Arguments BlockF {A}.
  Arguments DoneF {A}.
  Arguments StepF {A} [ptree] [neg_X pos_X].
  Arguments GuardF {A} [ptree] t.
  Arguments _observe {A}.
  Arguments go {A}.

  Notation ptree' A := (ptreeF A (ptree A)).

  Definition observe {A} (t : ptree A) : ptree' A := @_observe A t.

End PTree.

(*  (* Not a postive ocurrence *)
  CoInductive tree {A : Sig.t} :=
    {
      next : (A^+ -> tree -> Prop) -> (A^- -> tree -> Prop) -> tree
    }.
  *) 

  (* (* *)
  CoInductive tree {A : Sig.t} :=
    {
      forall In Ip,
         (In -> A^-) -> (In -> trees) →
         (Ip -> A^+) -> (Ip -> tree) →
         tree.
    }  
  *)

  (* (* *)
  CoInductive tree :=
  | node : (nat -> option (A^+ * tree)) →
          (nat -> option (A^- * tree)) →
          tree.

  *)

  (* (* *) 
    CoInductive tree {A : Sig.t} :=
    | node : list (A^+ * tree2) -> 
             list (A^- * tree2) -> 
              tree.
  *)
