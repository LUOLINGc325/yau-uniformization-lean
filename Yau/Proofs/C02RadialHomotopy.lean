import Yau.Proofs.C02ParametricSmooth
import Yau.Proofs.C02RadialWeights

/-! The actual radial homotopy integral is smooth. Its elementary norm gain
has the exact factor one half used at order zero in the radial frame bounds. -/

noncomputable section
open Set
open scoped Interval ContDiff
universe u
namespace Yau.Blueprint.C02Proof
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def radialHomotopy (T : E → E →L[ℝ] F) (x : E) : F :=
  ∫ t in (0 : ℝ)..1, t • (T (t • x) x)

theorem radialHomotopy_smooth (T : E → E →L[ℝ] F) (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (radialHomotopy T) := by
  have hG : ContDiff ℝ ∞ (fun p : E × ℝ => p.2 • (T (p.2 • p.1) p.1)) :=
    contDiff_snd.smul ((hT.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_fst)
  exact contDiff_intervalIntegral_smooth _ hG

theorem norm_radialHomotopy_le (T : E → E →L[ℝ] F) (x : E) (A : ℝ)
    (hA : 0 ≤ A) (hT : ∀ t ∈ Icc (0 : ℝ) 1, ‖T (t • x)‖ ≤ A) :
    ‖radialHomotopy T x‖ ≤ ‖x‖ / 2 * A := by
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖t • (T (t • x) x)‖ ≤ (‖x‖ * A) * t ^ (0 + 1) + (0 : ℝ) * 0 * t ^ 0 := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hTx := (T (t • x)).le_opNorm x
    have hTA := mul_le_mul_of_nonneg_right (hT t ht) (norm_nonneg x)
    calc
      t * ‖T (t • x) x‖ ≤ t * (A * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hTx.trans hTA) ht.1
      _ = _ := by simp only [pow_one, pow_zero, zero_mul, add_zero]; ring
  have hi := norm_integral_radial_weights 0 (fun t => t • (T (t • x) x)) (‖x‖ * A) 0
    (by simpa only [Nat.cast_zero] using hb)
  dsimp only [radialHomotopy]
  convert hi using 1 <;> norm_num <;> ring

theorem norm_radialHomotopy_le_on_ball (T : E → E →L[ℝ] F) {ρ A : ℝ}
    (hA : 0 ≤ A) (hT : ∀ y ∈ Metric.closedBall (0 : E) ρ, ‖T y‖ ≤ A)
    {x : E} (hx : x ∈ Metric.closedBall (0 : E) ρ) :
    ‖radialHomotopy T x‖ ≤ ρ / 2 * A := by
  have hx' : ‖x‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hRad : ∀ t ∈ Icc (0 : ℝ) 1, ‖T (t • x)‖ ≤ A := by
    intro t ht
    apply hT
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans hx'
  exact (norm_radialHomotopy_le T x A hA hRad).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hx' (by norm_num)) hA)

end Yau.Blueprint.C02Proof
