import Yau.LeafProofs.L10InteriorHessianResidual
import Yau.LeafProofs.L10InteriorCaccioppoli

/-! The actual coordinate Hessian and the original Fréchet tensor norm. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

def ellipticHessianEnergy {n : ℕ} (u : ComplexVector n → ℂ) (x : ComplexVector n) : ℝ :=
  ∑ k, ∑ i, ‖ellipticHessianField u x k i‖^2

theorem ellipticHessianField_eq_tensor {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O) (k i : RIdx n) :
    ellipticHessianField u x k i =
      iteratedFDeriv ℝ 2 u x ![realVec i, realVec k] := by
  have hu2 : ContDiffAt ℝ 2 u x := (hu.contDiffAt (hO.mem_nhds hx)).of_le (by simp)
  have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold ellipticHessianField
  rw [fderiv_clm_apply hD (show DifferentiableAt ℝ (fun _ : ComplexVector n => realVec k) x by fun_prop)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem ellipticHessianField_norm_le {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) {x : ComplexVector n} (hx : x ∈ O) (k i : RIdx n) :
    ‖ellipticHessianField u x k i‖ ≤ ‖iteratedFDeriv ℝ 2 u x‖ := by
  rw [ellipticHessianField_eq_tensor hO hu hx]
  have hn (j : RIdx n) : ‖realVec j‖ = 1 := by
    rw [← complexVector_realOrthonormalBasis_apply]
    exact (complexVector_realOrthonormalBasis n).norm_eq_one _
  simpa [Fin.prod_univ_two, hn] using
    (iteratedFDeriv ℝ 2 u x).le_opNorm ![realVec i, realVec k]

theorem ellipticHessianEnergy_integrableOn {n : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hi : IntegrableOn (fun x => ‖iteratedFDeriv ℝ 2 u x‖^2) O (lebesgueC n)) :
    IntegrableOn (ellipticHessianEnergy u) O (lebesgueC n) := by
  classical
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro i _
  have hc : ContinuousOn (fun x => ‖ellipticHessianField u x k i‖^2) O :=
    (elliptic_contDiffOn_directionalDerivative hO
      (elliptic_contDiffOn_directionalDerivative hO hu (realVec k)) (realVec i)).continuousOn.norm.pow 2
  apply hi.mono' (hc.aestronglyMeasurable hO.measurableSet)
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (ellipticHessianField_norm_le hO hu hx k i) 2

theorem ellipticHessianEnergy_weighted_integrableOn {n : ℕ}
    {u : ComplexVector n → ℂ} {η : ComplexVector n → ℝ}
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hu : ContDiffOn ℝ ∞ u O)
    (hη : ContDiff ℝ ∞ η) (hηBound : ∀ x, |η x| ≤ 1)
    (hi : IntegrableOn (fun x => ‖iteratedFDeriv ℝ 2 u x‖^2) O (lebesgueC n)) :
    IntegrableOn (fun x => (η x)^2 * ellipticHessianEnergy u x) O (lebesgueC n) := by
  have hQ := ellipticHessianEnergy_integrableOn hO hu hi
  have hWeight : ∀ x, ‖(η x)^2‖ ≤ 1 := by
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := hηBound x
    nlinarith [abs_nonneg (η x), sq_abs (η x)]
  simpa only [IntegrableOn, Pi.pow_apply, mul_comm] using hQ.mul_bdd
    ((hη.continuous.pow 2).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall hWeight)

end Yau.LeafProofs
