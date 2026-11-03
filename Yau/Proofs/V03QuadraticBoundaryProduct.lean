import Yau.Proofs.V03BoundaryCurrentEstimate
import Yau.Proofs.V03MatrixBoundaryEntryProduct

/-! Native half-order control of the exact coefficient-times-two-velocity
products that occur in the genuine base and Gauss boundary currents. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_quadratic_product_le {u B v : ℝ → ℂ}
    (hu : Continuous u) (hB : Continuous B) (hv : Continuous v)
    (hup : Function.Periodic u (2 * Real.pi))
    (hBp : Function.Periodic B (2 * Real.pi))
    (hvp : Function.Periodic v (2 * Real.pi))
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (huL : ∀ θ, ‖u θ‖ ≤ L) (hBM : ∀ θ, ‖B θ‖ ≤ M) (hvL : ∀ θ, ‖v θ‖ ≤ L) :
    boundaryDSq (fun θ (_ : Unit) => star (u θ) * B θ * v θ) ≤
      ENNReal.ofReal (2 * L ^ 2) *
        (ENNReal.ofReal (2 * M ^ 2) * boundaryDSq (fun θ (_ : Unit) => u θ) +
          ENNReal.ofReal (2 * L ^ 2) * boundaryDSq (fun θ (_ : Unit) => B θ)) +
        ENNReal.ofReal (2 * (L * M) ^ 2) * boundaryDSq (fun θ (_ : Unit) => v θ) := by
  have hus : Continuous (fun θ => star (u θ)) := hu.star
  have hsp : Function.Periodic (fun θ => star (u θ)) (2 * Real.pi) := fun θ => congrArg star (hup θ)
  have hsL : ∀ θ, ‖star (u θ)‖ ≤ L := by simpa only [norm_star] using huL
  have hfirst := boundaryDSq_mul_le hus hB hsp hBp hL hM hsL hBM
  rw [scalarDSq_conj hu hup] at hfirst
  have hprod (θ : ℝ) : ‖star (u θ) * B θ‖ ≤ L * M := by
    rw [norm_mul]
    exact mul_le_mul (hsL θ) (hBM θ) (norm_nonneg _) hL
  have hsecond := boundaryDSq_mul_le (hus.mul hB) hv (hsp.mul hBp) hvp
    (mul_nonneg hL hM) hL hprod hvL
  apply hsecond.trans
  gcongr
  simpa only [Pi.mul_apply] using hfirst

end Yau.Blueprint.V03Proof
