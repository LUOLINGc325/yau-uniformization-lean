import Yau.Proofs.P04CutoffModel

noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

def regularizedPoleModel (χ : ComplexVector n → ℝ) (z₀ : ComplexVector n)
    (c ε : ℝ) (z : ComplexVector n) : ℝ :=
  c*χ z*Real.log (‖z-z₀‖^2+ε^2)

theorem regularizedPoleModel_smooth {χ : ComplexVector n → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (z₀ : ComplexVector n) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (regularizedPoleModel χ z₀ c ε) := by
  have hq : ContDiff ℝ ∞ (fun z : ComplexVector n => ‖z-z₀‖^2+ε^2) :=
    ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).add contDiff_const
  have hpos (z : ComplexVector n) : 0 < ‖z-z₀‖^2+ε^2 := by positivity
  exact (contDiff_const.mul hχ).mul (hq.log (fun z => (hpos z).ne'))

theorem regularizedPoleModel_tsupport (χ : ComplexVector n → ℝ)
    (z₀ : ComplexVector n) (c ε : ℝ) :
    tsupport (regularizedPoleModel χ z₀ c ε) ⊆ tsupport χ := by
  apply closure_mono
  intro z hz hzero
  exact hz (by simp only [regularizedPoleModel,hzero,mul_zero,zero_mul])

theorem regularizedPoleModel_compact {χ : ComplexVector n → ℝ}
    (hχ : HasCompactSupport χ) (z₀ : ComplexVector n) (c ε : ℝ) :
    HasCompactSupport (regularizedPoleModel χ z₀ c ε) :=
  hχ.of_isClosed_subset (isClosed_tsupport _) (regularizedPoleModel_tsupport χ z₀ c ε)

theorem regularizedPoleModel_mono {χ : ComplexVector n → ℝ}
    (hχ : ∀ z, 0 ≤ χ z) (z₀ : ComplexVector n) {c ε δ : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε) (hεδ : ε ≤ δ) (z : ComplexVector n) :
    regularizedPoleModel χ z₀ c ε z ≤ regularizedPoleModel χ z₀ c δ z := by
  have hq : 0 < ‖z-z₀‖^2+ε^2 := by positivity
  have hle : ‖z-z₀‖^2+ε^2 ≤ ‖z-z₀‖^2+δ^2 := by nlinarith
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hq hle) (mul_nonneg hc (hχ z))

theorem regularizedPoleModel_nonpos {χ : ComplexVector n → ℝ}
    (hχ : ∀ z, 0 ≤ χ z) (z₀ : ComplexVector n) {c ρ ε : ℝ}
    (hc : 0 ≤ c) (hρ : 0 < ρ) (hsmall : 5*ρ^2 < 1)
    (hs : tsupport χ ⊆ Metric.closedBall z₀ (3*ρ/2))
    (hε : 0 < ε) (hερ : ε ≤ ρ) (z : ComplexVector n) :
    regularizedPoleModel χ z₀ c ε z ≤ 0 := by
  by_cases hz : χ z=0
  · simp only [regularizedPoleModel,hz,mul_zero,zero_mul,le_refl]
  · have hsupp : z ∈ tsupport χ := subset_closure hz
    have hnorm : ‖z-z₀‖ ≤ 3*ρ/2 := by
      simpa only [dist_eq_norm] using Metric.mem_closedBall.mp (hs hsupp)
    have hq : 0 < ‖z-z₀‖^2+ε^2 := by positivity
    have hq1 : ‖z-z₀‖^2+ε^2 ≤ 1 := by nlinarith [norm_nonneg (z-z₀)]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hc (hχ z)) (Real.log_nonpos hq.le hq1)

def poleEpsilon (ρ : ℝ) (j : ℕ) : ℝ := ρ/(j+2)

theorem poleEpsilon_pos {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) : 0 < poleEpsilon ρ j := by
  dsimp only [poleEpsilon]
  positivity

theorem poleEpsilon_le {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) : poleEpsilon ρ j ≤ ρ := by
  rw [poleEpsilon,div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ)+2)]
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith

theorem poleEpsilon_antitone {ρ : ℝ} (hρ : 0 < ρ) : Antitone (poleEpsilon ρ) := by
  intro i j hij
  change ρ/((j : ℝ)+2) ≤ ρ/((i : ℝ)+2)
  exact div_le_div_of_nonneg_left hρ.le (by positivity : (0 : ℝ) < (i : ℝ)+2)
    (by exact_mod_cast (show i+2 ≤ j+2 by omega))

end Yau.Proofs.P04Aux
