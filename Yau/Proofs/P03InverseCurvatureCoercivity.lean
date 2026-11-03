import Yau.Proofs.P03CoefficientCompletion

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Actual curvature coercivity bounds the frozen variational supremum by
the genuine source norm, including the zero-rank and zero-dimensional cases. -/
theorem inverseCurvatureNormSq_le_of_coercive
    (g : HermitianField M) (h : Metric (M := M) E) (φ : M.Carrier → ℝ)
    (f : NQForm E 1) (x : M.Carrier) (lam : ℝ) (hlam : 0 < lam)
    (hcoercive : ∀ V : Fin n → Fin r → ℂ,
      lam * (coefficientInner (r := r) E g h x V V).re ≤ curvatureEnergy (r := r) E g h φ x V) :
    inverseCurvatureNormSq (r := r) E g h φ f x ≤
      ENNReal.ofReal (lam⁻¹ * BundleDbar.formNormSq (r := r) E g h f x) := by
  let F : Fin n → Fin r → ℂ :=
    fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α
  apply iSup_le
  intro V
  apply ENNReal.ofReal_le_ofReal
  have hsq := coefficientInner_self_nonneg E g h x (F + (-lam : ℂ) • V)
  rw [coefficientInner_real_completion E g h x F V lam] at hsq
  have hb := mul_le_mul_of_nonneg_left (hcoercive V) hlam.le
  have hscaled : lam * (2 * (coefficientInner (r := r) E g h x F V).re -
      curvatureEnergy (r := r) E g h φ x V) ≤
      (coefficientInner (r := r) E g h x F F).re := by nlinarith
  calc
    2 * (coefficientInner (r := r) E g h x F V).re - curvatureEnergy (r := r) E g h φ x V =
        lam⁻¹ * (lam * (2 * (coefficientInner (r := r) E g h x F V).re -
          curvatureEnergy (r := r) E g h φ x V)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
    _ ≤ lam⁻¹ * (coefficientInner (r := r) E g h x F F).re :=
      mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hlam.le)
    _ = lam⁻¹ * BundleDbar.formNormSq (r := r) E g h f x := by
      rw [formNormSq_one_eq_coefficientInner]

end Yau.NodeProofs.P03Aux
