import Yau.Proofs.F04BilinearTimeMeasurability
import Yau.Proofs.F04BochnerL2
import Yau.LeafProofs.L16HilbertTimeRegularization

open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def variationalTimeBilinearLinear
    (B : ℝ → V →L[ℝ] W →L[ℝ] ℝ) (C : ℝ) (hB : ∀ t, ‖B t‖ ≤ C)
    (hc : ∀ u v, Continuous (fun t => B t u v)) (ν : Measure ℝ) :
    Lp V 2 ν →ₗ[ℝ] Lp W 2 ν →ₗ[ℝ] ℝ where
  toFun U :=
    { toFun := fun Z => ∫ t, B t (U t) (Z t) ∂ν
      map_add' := by
        intro Z Q
        have hiZ := bounded_bilinear_time_integrable B C hB hc ν (Lp.memLp U) (Lp.memLp Z)
        have hiQ := bounded_bilinear_time_integrable B C hB hc ν (Lp.memLp U) (Lp.memLp Q)
        calc
          _ = ∫ t, B t (U t) (Z t) + B t (U t) (Q t) ∂ν := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add Z Q] with t ht
            rw [ht]
            simp only [Pi.add_apply, map_add]
          _ = _ := integral_add hiZ hiQ
      map_smul' := by
        intro c Z
        calc
          _ = ∫ t, c * B t (U t) (Z t) ∂ν := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul c Z] with t ht
            rw [ht]
            simp only [Pi.smul_apply, map_smul, smul_eq_mul]
          _ = _ := integral_const_mul c _ }
  map_add' := by
    intro U Q
    ext Z
    have hiU := bounded_bilinear_time_integrable B C hB hc ν (Lp.memLp U) (Lp.memLp Z)
    have hiQ := bounded_bilinear_time_integrable B C hB hc ν (Lp.memLp Q) (Lp.memLp Z)
    calc
      _ = ∫ t, B t (U t) (Z t) + B t (Q t) (Z t) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add U Q] with t ht
        rw [ht]
        simp only [Pi.add_apply, map_add, add_apply]
      _ = _ := integral_add hiU hiQ
  map_smul' := by
    intro c U
    ext Z
    calc
      _ = ∫ t, c * B t (U t) (Z t) ∂ν := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c U] with t ht
        rw [ht]
        simp only [Pi.smul_apply, map_smul, smul_apply, smul_eq_mul]
      _ = _ := integral_const_mul c _

theorem variationalTimeBilinear_bound
    (B : ℝ → V →L[ℝ] W →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C) (hB : ∀ t, ‖B t‖ ≤ C)
    (hc : ∀ u v, Continuous (fun t => B t u v)) (ν : Measure ℝ)
    (U : Lp V 2 ν) (Z : Lp W 2 ν) :
    ‖variationalTimeBilinearLinear B C hB hc ν U Z‖ ≤ C * ‖U‖ * ‖Z‖ := by
  have hBi := bounded_bilinear_time_integrable B C hB hc ν (Lp.memLp U) (Lp.memLp Z)
  have hi := integral_mono hBi.norm (((Lp.memLp U).norm.integrable_mul (Lp.memLp Z).norm).const_mul C)
    (fun t => by
      simpa only [mul_assoc, Pi.mul_apply] using ((B t).le_opNorm₂ (U t) (Z t)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _)) (norm_nonneg _)))
  dsimp only [Pi.mul_apply] at hi
  rw [integral_const_mul] at hi
  have hHolder := Yau.LeafProofs.L16HilbertTimeRegularization.integral_norm_mul_le
    (Lp.memLp U) (Lp.memLp Z)
  rw [← bochner_l2_norm_sq_integral U, ← bochner_l2_norm_sq_integral Z,
    Real.sqrt_sq (norm_nonneg U), Real.sqrt_sq (norm_nonneg Z)] at hHolder
  exact (norm_integral_le_integral_norm (f := fun t => B t (U t) (Z t)) (μ := ν)).trans
    (hi.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hHolder hC))

/-- The time-integrated genuine form is an actual bounded bilinear operator
 on the Bochner Hilbert spaces, independent of representative choices. -/
def variationalTimeBilinear
    (B : ℝ → V →L[ℝ] W →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C) (hB : ∀ t, ‖B t‖ ≤ C)
    (hc : ∀ u v, Continuous (fun t => B t u v)) (ν : Measure ℝ) :
    Lp V 2 ν →L[ℝ] Lp W 2 ν →L[ℝ] ℝ :=
  (variationalTimeBilinearLinear B C hB hc ν).mkContinuous₂ C
    (variationalTimeBilinear_bound B C hC hB hc ν)

theorem variationalTimeBilinear_apply
    (B : ℝ → V →L[ℝ] W →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C) (hB : ∀ t, ‖B t‖ ≤ C)
    (hc : ∀ u v, Continuous (fun t => B t u v)) (ν : Measure ℝ)
    (U : Lp V 2 ν) (Z : Lp W 2 ν) :
    variationalTimeBilinear B C hC hB hc ν U Z = ∫ t, B t (U t) (Z t) ∂ν := rfl

theorem variationalTimeBilinear_section_norm_le
    (B : ℝ → V →L[ℝ] W →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C) (hB : ∀ t, ‖B t‖ ≤ C)
    (hc : ∀ u v, Continuous (fun t => B t u v)) (ν : Measure ℝ) (U : Lp V 2 ν) :
    ‖variationalTimeBilinear B C hC hB hc ν U‖ ≤ C * ‖U‖ := by
  apply (variationalTimeBilinear B C hC hB hc ν U).opNorm_le_bound (mul_nonneg hC (norm_nonneg U))
  exact variationalTimeBilinear_bound B C hC hB hc ν U

end Yau.F04Proof
