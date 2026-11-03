import Yau.LeafProofs.L03

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def centerFormReconstruction (x : M.Carrier) :
    ((Fin k → RIdx n) → ℝ) →L[ℝ] ((TangentVector M x)[⋀^Fin k]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.compContinuousLinearMapCLM (tangentCoordsRealContinuousLinearMap x x)).comp
    (modelFormReconstruction n k)

theorem centerFormReconstruction_coeff (A : RealForm M k) (x : M.Carrier) :
    centerFormReconstruction x (formComponents A x (chartPt x x)) = A x := by
  change ((modelFormReconstruction n k)
    ((modelFormCoefficientMap n k) (chartForm A x (chartPt x x)))).compContinuousLinearMap
      (tangentCoordsRealContinuousLinearMap x x) = A x
  rw [modelFormReconstruction_coefficient]
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  apply ContinuousAlternatingMap.ext
  intro v
  change A (chartInv x (chartPt x x))
    (fun r => chartVec x (chartInv x (chartPt x x)) (tangentCoords x x (v r))) = A x v
  rw [hx]
  congr 1
  funext r
  exact L12Aux.chartVec_tangentCoords x x (mem_extChartAt_source x) (v r)

theorem center_coefficient_abs_le_metric (g : HermitianField M) (x : M.Carrier)
    (I : Fin k → RIdx n) : ∃ C : ℝ, 0 ≤ C ∧ ∀ A : RealForm M k,
      |formComponents A x (chartPt x x) I| ≤ C * Real.sqrt (formNormSq g A x) := by
  let D := (Nat.factorial k : ℝ) * ∏ r, realMetricFn g x (chartPt x x) (I r) (I r)
  let C := Real.sqrt (max D 0)
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro A
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hb := formComponents_sq_le_metric g A x (mem_extChartAt_target x) I
  change (formComponents A x (chartPt x x) I) ^ 2 ≤ D * formNormSq g A (chartInv x (chartPt x x)) at hb
  rw [hx] at hb
  have hn := formNormSq_nonneg g A x
  have hc : C ^ 2 = max D 0 := Real.sq_sqrt (le_max_right _ _)
  have hs : Real.sqrt (formNormSq g A x) ^ 2 = formNormSq g A x := Real.sq_sqrt hn
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [sq_abs, mul_pow, hc, hs]
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left D 0) hn)

/-- Convergence in the actual finite-dimensional alternating fibre
preserves the frozen metric quadratic form at that point. -/
theorem formNormSq_tendsto_of_fiber_tendsto (g : HermitianField M)
    (As : ℕ → RealForm M k) (A : RealForm M k) (x : M.Carrier)
    (ht : Tendsto (fun m => As m x) atTop (𝓝 (A x))) :
    Tendsto (fun m => formNormSq g (As m) x) atTop (𝓝 (formNormSq g A x)) := by
  classical
  letI : ContinuousSMul ℝ (TangentVector M x) := IsScalarTower.continuousSMul ℂ
  let C := (Fin k → RIdx n) → ℝ
  let P : Matrix (Fin k → RIdx n) (Fin k → RIdx n) ℝ :=
    fun I J => ∏ r, (realMetricFn g x (chartPt x x))⁻¹ (I r) (J r)
  let Q : C → ℝ := fun v => (Nat.factorial k : ℝ)⁻¹ * dotProduct v (Matrix.mulVec P v)
  have hQ : Continuous Q := by
    dsimp only [Q, dotProduct, Matrix.mulVec]
    fun_prop
  have hc (I : Fin k → RIdx n) : Tendsto (fun m => formComponents (As m) x (chartPt x x) I)
      atTop (𝓝 (formComponents A x (chartPt x x) I)) := by
    simp only [formComponents_center_apply]
    exact ((ContinuousAlternatingMap.apply ℝ (TangentVector M x) ℝ
      (fun r => (tangentSpaceCastModel (ComplexModel n) x).symm (realVec (I r)))).continuous.tendsto (A x)).comp ht
  have he (B : RealForm M k) : Q (formComponents B x (chartPt x x)) = formNormSq g B x := by
    rw [formNormSq_eq_matrix]
    simp only [Q, P, star_trivial]
  simpa only [Function.comp_def, he] using (hQ.tendsto (formComponents A x (chartPt x x))).comp (tendsto_pi_nhds.mpr hc)

end Yau.LeafProofs.L03
