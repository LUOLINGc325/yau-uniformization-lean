import Yau.LeafProofs.L19Differential
import Yau.LeafProofs.L19Harnack

/-! Two applications of the genuine Harnack estimate to the original
symmetric scalar heat kernel. -/

noncomputable section
open MeasureTheory
open scoped ComplexOrder
namespace Yau.LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000

theorem scalarHeatKernel_double_harnack (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {μ : Measure M.Carrier} {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H)
    {s t T : ℝ} (hs : 0 < s) (hst : s < t) (htT : t < T)
    (x y z w : M.Carrier) :
    H s x y ≤ (T / s) ^ n *
      Real.exp (inducedDistance g.form x z ^ 2 / (2 * (t - s)) +
        inducedDistance g.form y w ^ 2 / (2 * (T - t))) * H T z w := by
  have ht : 0 < t := lt_trans hs hst
  have hT : 0 < T := lt_trans ht htT
  have h1 := positiveHeatSolution_harnack liYauDifferential g hcomplete hK hRic (hH.1 y) hs hst x z
  have h2 := positiveHeatSolution_harnack liYauDifferential g hcomplete hK hRic (hH.1 z) ht htT y w
  rw [hH.2.1 t ht z y] at h1
  rw [hH.2.1 T hT w z] at h2
  have hrat : (t / s) * (T / t) = T / s := by field_simp
  calc
    H s x y ≤ (t / s) ^ n * Real.exp (inducedDistance g.form x z ^ 2 / (2 * (t - s))) * H t y z := h1
    _ ≤ (t / s) ^ n * Real.exp (inducedDistance g.form x z ^ 2 / (2 * (t - s))) *
        ((T / t) ^ n * Real.exp (inducedDistance g.form y w ^ 2 / (2 * (T - t))) * H T z w) := by
      apply mul_le_mul_of_nonneg_left h2
      exact mul_nonneg (pow_nonneg (div_nonneg ht.le hs.le) _) (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_add, ← hrat, mul_pow]; ring

theorem scalarHeatKernel_triple_time_harnack (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {μ : Measure M.Carrier} {H : ℝ → M.Carrier → M.Carrier → ℝ}
    (hH : LeafCandidates.ScalarHeatKernel g.form μ H) {t : ℝ} (ht : 0 < t)
    (x y z w : M.Carrier)
    (hz : inducedDistance g.form x z ≤ Real.sqrt t)
    (hw : inducedDistance g.form y w ≤ Real.sqrt t) :
    H t x y ≤ (3 : ℝ) ^ n * Real.exp 1 * H (3 * t) z w := by
  have h1 := scalarHeatKernel_double_harnack g hcomplete hK hRic hH ht
    (show t < 2 * t by linarith) (show 2 * t < 3 * t by linarith) x y z w
  have hdistz : inducedDistance g.form x z ^ 2 ≤ t := by
    have hsq := Real.sq_sqrt ht.le
    nlinarith [g.induced_distance_nonneg x z, Real.sqrt_nonneg t]
  have hdistw : inducedDistance g.form y w ^ 2 ≤ t := by
    have hsq := Real.sq_sqrt ht.le
    nlinarith [g.induced_distance_nonneg y w, Real.sqrt_nonneg t]
  have he : inducedDistance g.form x z ^ 2 / (2 * (2 * t - t)) +
      inducedDistance g.form y w ^ 2 / (2 * (3 * t - 2 * t)) ≤ 1 := by
    rw [show 2 * t - t = t by ring, show 3 * t - 2 * t = t by ring, ← add_div]
    exact (div_le_one (mul_pos (by norm_num) ht)).mpr (by linarith)
  have hrat : 3 * t / t = 3 := by field_simp
  rw [hrat] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity))
      ((hH.1 w).2 z (3 * t) (by positivity)).1.le)

end Yau.LeafProofs.L19Aux
