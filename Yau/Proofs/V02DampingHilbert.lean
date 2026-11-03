import Yau.Proofs.V02DampingAlgebra

/-! A dimension-independent Lipschitz bound for the actual logarithmic
damping on a real Hilbert space. It applies to every finite complex matrix
after realification. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02Proof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_innerSL_le_norm (v : H) : ‖innerSL ℝ v‖ ≤ ‖v‖ :=
  (innerSL ℝ v).opNorm_le_bound (norm_nonneg v) (fun w => norm_inner_le_norm v w)

theorem dampingLog_fderiv_norm_bound {P : ℝ} (hP : 0 < P) (v : H) :
    ‖fderiv ℝ (fun v : H => Real.log (P + ‖v‖ ^ 2)) v‖ ≤ (Real.sqrt P)⁻¹ := by
  have hden : 0 < P + ‖v‖ ^ 2 := by positivity
  have hd := (((hasStrictFDerivAt_norm_sq v).hasFDerivAt).const_add P).log hden.ne'
  rw [hd.fderiv]
  calc
    ‖(P + ‖v‖ ^ 2)⁻¹ • (2 • innerSL ℝ v)‖ ≤
        (P + ‖v‖ ^ 2)⁻¹ * 2 * ‖innerSL ℝ v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden)]
      have htwo : ‖(2 : ℕ) • innerSL ℝ v‖ ≤ 2 * ‖innerSL ℝ v‖ := norm_nsmul_le
      simpa only [Nat.cast_ofNat, mul_assoc] using
        mul_le_mul_of_nonneg_left htwo
          (by positivity : 0 ≤ (P + ‖v‖ ^ 2)⁻¹)
    _ ≤ (P + ‖v‖ ^ 2)⁻¹ * 2 * ‖v‖ :=
      mul_le_mul_of_nonneg_left (norm_innerSL_le_norm v) (by positivity)
    _ = 2 * ‖v‖ / (P + ‖v‖ ^ 2) := by ring
    _ ≤ _ := dampingLog_radial_derivative_bound hP (norm_nonneg v)

theorem dampingLog_lipschitz {P : ℝ} (hP : 0 < P) :
    LipschitzWith (Real.toNNReal ((Real.sqrt P)⁻¹))
      (fun v : H => Real.log (1 + ‖v‖ ^ 2 / P)) := by
  have hbase : Differentiable ℝ (fun v : H => Real.log (P + ‖v‖ ^ 2)) := by
    intro v
    exact ((((hasStrictFDerivAt_norm_sq v).hasFDerivAt).const_add P).log
      (by positivity : P + ‖v‖ ^ 2 ≠ 0)).differentiableAt
  have hLip : LipschitzWith (Real.toNNReal ((Real.sqrt P)⁻¹))
      (fun v : H => Real.log (P + ‖v‖ ^ 2)) :=
    lipschitzWith_of_nnnorm_fderiv_le hbase (fun v => by
      apply NNReal.coe_le_coe.mp
      exact (dampingLog_fderiv_norm_bound hP v).trans (Real.le_coe_toNNReal _))
  have heq (v : H) : Real.log (1 + ‖v‖ ^ 2 / P) =
      Real.log (P + ‖v‖ ^ 2) - Real.log P := by
    have hfrac : 1 + ‖v‖ ^ 2 / P = (P + ‖v‖ ^ 2) / P := by field_simp
    rw [hfrac, Real.log_div (by positivity : P + ‖v‖ ^ 2 ≠ 0) hP.ne']
  apply LipschitzWith.of_dist_le_mul
  intro u v
  rw [heq u, heq v, dist_sub_right]
  exact hLip.dist_le_mul u v

end Yau.Blueprint.V02Proof
