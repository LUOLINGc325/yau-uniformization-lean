import Yau.Proofs.P04HolomorphicVectorLevi
import Yau.Proofs.P04FiniteCoefficientVector

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau

/-- The actual selected finite partial sums satisfy the numerator inequality
also where every coefficient vanishes. -/
theorem finite_sumSquares_numerator {n : ℕ} (N : ℕ) (c : ℕ → ℝ)
    (f : ℕ → ComplexVector n → ℂ) (hc : ∀ i, 0 ≤ c i) {z : ComplexVector n}
    (hf : ∀ i < N, ContDiffAt ℂ 2 (f i) z) :
    (((∑ i ∈ Finset.range N, c i*‖f i z‖^2 : ℝ) : ℂ) •
      leviC (fun y => ∑ i ∈ Finset.range N, c i*‖f i y‖^2) z-
      gradientGram (fun y => ∑ i ∈ Finset.range N, c i*‖f i y‖^2) z).PosSemidef := by
  have H := holomorphic_vectorNormSq_numerator (finiteCoefficientVector_contDiffAt c f hf)
  have heq : (fun y => ‖finiteCoefficientVector N c f y‖^2) =
      fun y => ∑ i ∈ Finset.range N, c i*‖f i y‖^2 :=
    funext (finiteCoefficientVector_norm_sq N c f hc)
  change (((((fun y => ‖finiteCoefficientVector N c f y‖^2) z : ℝ) : ℂ)) •
    leviC (fun y => ‖finiteCoefficientVector N c f y‖^2) z-
    gradientGram (fun y => ‖finiteCoefficientVector N c f y‖^2) z).PosSemidef at H
  rwa [heq] at H

end Yau.Proofs.P04Aux
