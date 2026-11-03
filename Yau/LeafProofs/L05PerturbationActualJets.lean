import Yau.LeafProofs.L05PerturbationActualJetsSpatial
import Yau.LeafProofs.L05PerturbationActualJetsTime

open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section

namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- A high-order local polynomial approximation identifies the actual parabolic jets,
including the original causal derivative at the terminal face. -/
theorem perturb_identify_polynomial {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) {eta E r0 c q : ℝ}
    (heta : 0 < eta) (hE : 0 ≤ E) (hr0 : 0 < r0) (hr01 : r0 < 1)
    (b : Space n →L[ℝ] ℝ) (A : Sym n)
    (herr : ∀ r : ℝ, 0 < r → r ≤ r0 →
      ∀ p ∈ perturbClosed (0 : Space n) r 0,
        |u p - perturbPolynomial c b A q p| ≤ E * r ^ (2 + eta)) :
    c = u (0, 0) ∧ b = spatialD u (0, 0) ∧ A = hessian u (0, 0) ∧
      q = timeD (backward 1) u (0, 0) := by
  have hc0 : u (0, 0) - c = 0 := perturb_actual_constant_zero hr0
    (by linarith : 0 < 2 + eta) (by
      intro r hr hrb
      have hp : ((0, 0) : Point n) ∈ perturbClosed (0 : Space n) r 0 :=
        ⟨mem_closedBall_self hr.le, by nlinarith [sq_nonneg r], le_rfl⟩
      simpa [perturbPolynomial, perturbQuad_eq_bilinear] using herr r hr hrb (0, 0) hp)
  have hc : c = u (0, 0) := (sub_eq_zero.mp hc0).symm
  obtain ⟨hb, hA⟩ := perturb_actual_spatial_identification hu heta hr0 b A hc herr
  exact ⟨hc, hb, hA, perturb_actual_time_identification hu heta hr0 b A hc herr⟩

end Yau.LeafProofs.L05Aux
