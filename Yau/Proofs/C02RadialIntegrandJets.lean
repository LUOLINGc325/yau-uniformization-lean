import Yau.Proofs.C02LinearFactorJets

/-! Sharp derivatives of the radial integrand. Both powers of the radial
parameter are retained, so the highest-order absorption uses one fixed radius. -/

noncomputable section
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_radial_integrand_le
    (T : E → E →L[ℝ] F) (hT : ContDiff ℝ ∞ T)
    (k : ℕ) (x : E) (t : ℝ) (ht : 0 ≤ t) :
    ‖iteratedFDeriv ℝ (k + 1) (fun y => t • (T (t • y) y)) x‖ ≤
      t ^ (k + 2) * ‖iteratedFDeriv ℝ (k + 1) T (t • x)‖ * ‖x‖ +
        ((k : ℝ) + 1) * t ^ (k + 1) * ‖iteratedFDeriv ℝ k T (t • x)‖ := by
  let S : E → E →L[ℝ] F := fun y => T (t • y)
  have hS : ContDiff ℝ ∞ S := hT.comp (contDiff_const.smul contDiff_id)
  have hApply : ContDiff ℝ ∞ (fun y => S y y) := hS.clm_apply contDiff_id
  have hSjet (m : ℕ) : ‖iteratedFDeriv ℝ m S x‖ =
      t ^ m * ‖iteratedFDeriv ℝ m T (t • x)‖ := by
    rw [congrFun (iteratedFDeriv_comp_const_smul t
      (hT.of_le (show (m : ℕ∞ω) ≤ ∞ by simp))) x,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht m)]
  have hbase := norm_iteratedFDeriv_apply_identity_le S hS k x
  rw [hSjet (k + 1), hSjet k] at hbase
  calc
    _ = t * ‖iteratedFDeriv ℝ (k + 1) (fun y => S y y) x‖ := by
      change ‖iteratedFDeriv ℝ (k + 1) (fun y => t • (S y y)) x‖ = _
      rw [iteratedFDeriv_const_smul_apply'
        (hApply.contDiffAt.of_le (show ((k + 1 : ℕ) : ℕ∞ω) ≤ ∞ by simp)),
        norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    _ ≤ t * (t ^ (k + 1) * ‖iteratedFDeriv ℝ (k + 1) T (t • x)‖ * ‖x‖ +
        ((k : ℝ) + 1) * (t ^ k * ‖iteratedFDeriv ℝ k T (t • x)‖)) :=
      mul_le_mul_of_nonneg_left hbase ht
    _ = _ := by simp only [pow_succ]; ring

end Yau.Blueprint.C02Proof
