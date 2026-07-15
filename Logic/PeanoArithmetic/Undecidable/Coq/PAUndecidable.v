From Undecidability Require Import Synthetic.Definitions.
From Undecidability Require Import Synthetic.Undecidability.
From Undecidability.H10 Require Import H10p H10p_undec.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Reductions Require Import H10p_to_FA.

(** Syntactic provability from the usual first-order PA axiom schema. *)
Definition PA_theoremhood := deduction_PA.

(** Hilbert's tenth problem many-one reduces to PA theoremhood: a
    Diophantine equation is solvable exactly when PA proves its existential
    arithmetic translation. *)
Theorem H10p_reduces_to_PA_theoremhood :
  H10p ⪯ PA_theoremhood.
Proof.
  exact H10_to_deduction_PA.
Qed.

(** There is no total computable Boolean decider for syntactic PA
    theoremhood. *)
Theorem peano_arithmetic_theoremhood_not_decidable :
  undecidable PA_theoremhood.
Proof.
  refine (undecidability_from_reducibility _
            H10p_reduces_to_PA_theoremhood).
  exact H10p_undec.
Qed.
