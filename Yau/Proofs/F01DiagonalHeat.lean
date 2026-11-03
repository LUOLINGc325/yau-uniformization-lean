import Yau.Proofs.F01PenalizedHeatChain
import Yau.Proofs.F01HeatAtMaximum
import Yau.Proofs.F01WeightedCovectorCauchy
import Yau.Proofs.F01DiagonalCovectorNorm

/-! Fixed definitions of the actual local heat operator and covector
norm in a positive diagonal frame, with the original one-sided time derivative. -/
noncomputable section
open scoped ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

def diagonalHeatWithin (values : Fin n → ℝ) (F : ComplexVector n × ℝ → ℝ)
    (I : Set ℝ) (z : ComplexVector n) (t : ℝ) : ℝ :=
  derivWithin (fun s => F (z, s)) I t -
    traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC (fun w => F (w, t)) z)

def diagonalCovectorJet (f : ComplexVector n → ℝ) (z : ComplexVector n) : Fin n → ℂ :=
  fun i => wirt (fun w => (f w : ℂ)) z (stdVec i)

def diagonalGradientNorm (values : Fin n → ℝ) (f : ComplexVector n → ℝ)
    (z : ComplexVector n) : ℝ :=
  dualNormMat (Matrix.diagonal (fun i => (values i : ℂ)))
    (WithLp.toLp 2 (diagonalCovectorJet f z))

theorem diagonalGradientNorm_eq_weighted (values : Fin n → ℝ)
    (hv : ∀ i, values i ≠ 0) (f : ComplexVector n → ℝ) (z : ComplexVector n) :
    diagonalGradientNorm values f z =
      weightedCovectorSquare (fun i => (values i)⁻¹) (diagonalCovectorJet f z) :=
  dualNormMat_real_diagonal values hv _

theorem diagonalHeatWithin_nonneg_at_max (values : Fin n → ℝ) (hv : ∀ i, 0 < values i)
    (F : ComplexVector n × ℝ → ℝ) {z : ComplexVector n} {t T : ℝ}
    (ht : 0 < t) (htT : t ≤ T)
    (hspace : ContDiffAt ℝ 2 (fun w => F (w, t)) z)
    (hmaxSpace : IsLocalMax (fun w => F (w, t)) z)
    (htime : DifferentiableWithinAt ℝ (fun s => F (z, s)) (Set.Icc 0 T) t)
    (hmaxTime : IsMaxOn (fun s => F (z, s)) (Set.Icc 0 T) t) :
    0 ≤ diagonalHeatWithin values F (Set.Icc 0 T) z t :=
  complex_heat_nonneg_at_max values hv F ht htT hspace hmaxSpace htime hmaxTime

theorem diagonalHeatWithin_penalty_chain (values : Fin n → ℝ) (hv : ∀ i, values i ≠ 0)
    (U Q : ComplexVector n × ℝ → ℝ) (f : ComplexVector n → ℝ) (F : ℝ → ℝ)
    {z : ComplexVector n} {t δ : ℝ} {I : Set ℝ}
    (hUnique : UniqueDiffWithinAt ℝ I t)
    (hUtime : DifferentiableWithinAt ℝ (fun s => U (z, s)) I t)
    (hQtime : DifferentiableWithinAt ℝ (fun s => Q (z, s)) I t)
    (hUspace : ContDiffAt ℝ 2 (fun w => U (w, t)) z)
    (hQspace : ContDiffAt ℝ 2 (fun w => Q (w, t)) z)
    (hf : ContDiffAt ℝ 2 f z) (hF : ContDiffAt ℝ 2 F (Q (z, t))) :
    diagonalHeatWithin values (fun p => U p - F (Q p) - δ * f p.1) I z t =
      diagonalHeatWithin values U I z t -
      deriv F (Q (z, t)) * diagonalHeatWithin values Q I z t +
      deriv (deriv F) (Q (z, t)) * diagonalGradientNorm values (fun w => Q (w, t)) z +
      δ * traceWith (Matrix.diagonal (fun i => (values i : ℂ))) (leviC f z) :=
  penalized_heat_chain_within values hv U Q f F hUnique hUtime hQtime hUspace hQspace hf hF

end Yau.NodeProofs.F01Aux
