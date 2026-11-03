import Yau.Proofs.P03ManifoldPole
import Yau.Proofs.P03PoleRegularizationJoint

open scoped Manifold Topology ContDiff
open Filter Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem poleEpsilon_tendsto_zero : Tendsto poleEpsilon atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 4 : ℝ)
  convert h using 1
  · funext j
    simp only [poleEpsilon, one_div, mul_inv_rev]
    ring
  · ring

theorem manifoldCutoffPole_antitone (c : ℝ) (hc : 0 ≤ c) {a : M.Carrier}
    (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a) (x : M.Carrier) :
    Antitone (fun j => manifoldCutoffPole c b (poleEpsilon j) x) := by
  intro i j hij
  apply mul_le_mul_of_nonneg_left _ hc
  apply mul_le_mul_of_nonneg_left _ b.nonneg
  exact modelLogPole_mono_epsilon (chartPt a a) (chartPt a x)
    (poleEpsilon_pos j) (poleEpsilon_antitone hij)

theorem manifoldCutoffPole_nonpos (c : ℝ) (hc : 0 ≤ c) {a : M.Carrier}
    (b : SmoothBumpFunction 𝓘(ℝ, ComplexVector n) a) (hR : b.rOut ≤ 1 / 2)
    (j : ℕ) (x : M.Carrier) : manifoldCutoffPole c b (poleEpsilon j) x ≤ 0 := by
  by_cases hb : b x = 0
  · simp only [manifoldCutoffPole, hb, zero_mul, mul_zero, le_refl]
  · have hs : x ∈ Function.support (b : M.Carrier → ℝ) := hb
    rw [b.support_eq_inter_preimage] at hs
    have hn : ‖chartPt a x - chartPt a a‖ ≤ 1 / 2 := by
      have hd := Metric.mem_ball.mp hs.2
      change dist (chartPt a x) (chartPt a a) < b.rOut at hd
      rw [dist_eq_norm] at hd
      exact hd.le.trans hR
    have hq : ‖chartPt a x - chartPt a a‖ ^ 2 + poleEpsilon j ≤ 1 := by
      have hn0 := norm_nonneg (chartPt a x - chartPt a a)
      have hε := poleEpsilon_le_quarter j
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos hc
      (mul_nonpos_of_nonneg_of_nonpos b.nonneg
        (modelLogPole_nonpos (chartPt a a) (chartPt a x) (poleEpsilon_pos j) hq))

theorem modelLogPole_sequence_tendsto_away {n : ℕ} (a z : ComplexVector n) (hz : z ≠ a) :
    Tendsto (fun j => modelLogPole a (poleEpsilon j) z) atTop
      (𝓝 (Real.log (‖z - a‖ ^ 2))) := by
  simpa only [Function.comp_def, modelLogPole, add_zero] using
    (modelLogPole_continuousAt_epsilon_zero a z hz).tendsto.comp poleEpsilon_tendsto_zero

end Yau.NodeProofs.P03Aux
