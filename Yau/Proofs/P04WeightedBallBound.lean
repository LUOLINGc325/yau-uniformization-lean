import Yau.LeafProofs.L18

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Yau.Proofs.P04Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The genuine linear weight bounds the unweighted unit-ball integral by
the SAME global weighted norm, in the actual computed distance. -/
theorem unitBall_integral_le_weighted (g : SmoothMetric M) (μ : Measure M.Carrier)
    (o x : M.Carrier) (u ψ : M.Carrier → ℝ) (hu : ∀ y, 0 ≤ u y)
    {k C : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hψ : ∀ y, ψ y ≤ C*(1+distFrom g.form o y)) :
    (∫⁻ y in distBall g.form x 1, ENNReal.ofReal (u y) ∂μ) ≤
      ENNReal.ofReal (Real.exp (k*C*(2+distFrom g.form o x)))*
        ∫⁻ y, ENNReal.ofReal (u y*Real.exp (-(k*ψ y))) ∂μ := by
  letI := L12Aux.inducedMetricSpace g
  have hpoint (y : M.Carrier) (hy : y ∈ distBall g.form x 1) :
      u y ≤ Real.exp (k*C*(2+distFrom g.form o x))*(u y*Real.exp (-(k*ψ y))) := by
    have hy' := (L12Aux.mem_distBall_iff g x y (by norm_num : (0 : ℝ) < 1)).mp hy
    have hry : distFrom g.form o y ≤ distFrom g.form o x+1 := by
      have H := dist_triangle o x y
      change dist x y < 1 at hy'
      change dist o y ≤ dist o x+1
      linarith
    have hψbound : k*ψ y ≤ k*C*(2+distFrom g.form o x) := by
      have H := mul_le_mul_of_nonneg_left hry hC
      have Hψ := hψ y
      have Hψ' : ψ y ≤ C*(2+distFrom g.form o x) := by nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left Hψ' hk
    have heq : u y=(u y*Real.exp (-(k*ψ y)))*Real.exp (k*ψ y) := by
      rw [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
    nth_rw 1 [heq]
    calc
      _ ≤ (u y*Real.exp (-(k*ψ y)))*Real.exp (k*C*(2+distFrom g.form o x)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hψbound)
          (mul_nonneg (hu y) (Real.exp_pos _).le)
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∫⁻ y in distBall g.form x 1,
        ENNReal.ofReal (Real.exp (k*C*(2+distFrom g.form o x)))*
          ENNReal.ofReal (u y*Real.exp (-(k*ψ y))) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (L12Aux.measurableSet_distBall g x 1)] with y hy
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (hpoint y hy)
    _ = ENNReal.ofReal (Real.exp (k*C*(2+distFrom g.form o x)))*
        ∫⁻ y in distBall g.form x 1, ENNReal.ofReal (u y*Real.exp (-(k*ψ y))) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end Yau.Proofs.P04Aux
