import Yau.Proofs.P04RegularizedLogPole
import Yau.Proofs.P04PoleWeightModel
import Yau.LeafProofs.L17RicciNaturality

noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem leviC_zero (z : ComplexVector n) : leviC (fun _ : ComplexVector n => (0 : ℝ)) z=0 := by
  ext i j
  simp [leviC,leviMatrix,wirt,wirtBar]

/-- The cutoff is exactly one on a neighborhood of every inner-ball point. -/
theorem regularizedPoleModel_levi_inner {χ : ComplexVector n → ℝ}
    (z₀ : ComplexVector n) {ρ : ℝ}
    (hone : ∀ z ∈ Metric.closedBall z₀ ρ, χ z=1)
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    {z : ComplexVector n} (hz : z ∈ Metric.ball z₀ ρ) :
    (leviC (regularizedPoleModel χ z₀ c ε) z).PosSemidef := by
  have heq : regularizedPoleModel χ z₀ c ε =ᶠ[𝓝 z]
      (fun w => c*Real.log (poleQuadratic z₀ ε w)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    simp only [regularizedPoleModel,hone w (Metric.ball_subset_closedBall hw),mul_one,poleQuadratic]
  have hq : ContDiffAt ℝ 2 (fun w => Real.log (poleQuadratic z₀ ε w)) z :=
    ((poleQuadratic_smooth z₀ ε).contDiffAt.of_le (by simp)).log
      (by unfold poleQuadratic; positivity)
  rw [L22Aux.leviC_congr_of_eventuallyEq heq,L17Aux.leviC_const_mul hq c]
  exact (leviC_log_poleQuadratic_posSemidef z₀ hε z).smul (Complex.zero_le_real.mpr hc)

theorem regularizedPoleModel_levi_off_support {χ : ComplexVector n → ℝ}
    (z₀ : ComplexVector n) (c ε : ℝ) {z : ComplexVector n} (hz : z ∉ tsupport χ) :
    leviC (regularizedPoleModel χ z₀ c ε) z=0 := by
  have heq : regularizedPoleModel χ z₀ c ε =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz] with w hw
    simp only [regularizedPoleModel,image_eq_zero_of_notMem_tsupport hw,mul_zero,zero_mul]
  rw [L22Aux.leviC_congr_of_eventuallyEq heq,leviC_zero]

end Yau.Proofs.P04Aux
