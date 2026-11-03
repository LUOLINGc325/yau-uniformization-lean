import Yau.Proofs.D02JacobianTransition

/-! The actual covectors dF_a and their same-metric squared differential norm.
The covector coordinates are the rows of the computed Jacobian. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

/-- The differential of the actual a-th component of F, as a genuine covector. -/
def immersionComponentDifferential (F : M.Carrier → ComplexVector N) (a : Fin N)
    (y : M.Carrier) : Covector n :=
  (EuclideanSpace.proj a : ComplexVector N →L[ℂ] ℂ).comp
    ((NormedSpace.fromTangentSpace (𝕜 := ℂ) (F y)).toContinuousLinearMap.comp
      ((mfderiv (ComplexModel n) (ComplexModel N) F y).comp
        (tangentSpaceCastModel (ComplexModel n) y).symm.toContinuousLinearMap))

theorem immersionComponentDifferential_coords {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) x).source) (a : Fin N) :
    covectorCoords x y (immersionComponentDifferential F a y) =
      WithLp.toLp 2 (fun b => immersionDerivativeMatrix F x (chartPt x y) a b) := by
  ext b
  have h := immersionDerivativeMatrix_apply hF x (z := chartPt x y)
    ((extChartAt (ComplexModel n) x).map_source hy) a b
  have hround : chartInv x (chartPt x y) = y := (extChartAt (ComplexModel n) x).left_inv hy
  rw [hround] at h
  exact h.symm

/-- No free norm is supplied: u is computed from dF and the same g. -/
def immersionDifferentialNormSq (g : HermitianField M) (F : M.Carrier → ComplexVector N)
    (y : M.Carrier) : ℝ := ∑ a, dualNorm g y (immersionComponentDifferential F a y)

theorem immersionDifferentialNormSq_nonneg (g : HermitianField M)
    (F : M.Carrier → ComplexVector N) (y : M.Carrier) :
    0 ≤ immersionDifferentialNormSq g F y :=
  Finset.sum_nonneg fun a _ => dualNorm_nonneg g y (immersionComponentDifferential F a y)

theorem immersionDifferentialNormSq_in_fixed_chart (g : HermitianField M)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    immersionDifferentialNormSq g F (chartInv x z) =
      ∑ a, dualNormMat (hMat g x z)
        (WithLp.toLp 2 (fun b => immersionDerivativeMatrix F x z a b)) := by
  have hy := (extChartAt (ComplexModel n) x).map_target hz
  have hround : chartPt x (chartInv x z) = z := (extChartAt (ComplexModel n) x).right_inv hz
  unfold immersionDifferentialNormSq
  apply Finset.sum_congr rfl
  intro a _
  rw [dualNorm_eq_fixed_chart g x (chartInv x z) hy,
    immersionComponentDifferential_coords hF x (chartInv x z) hy a, hround]
  rfl

/-- The same dF norm is globally smooth for an arbitrary same-metric smooth field. -/
theorem immersionDifferentialNormSq_smooth (g : HermitianField M) (hg : MetricSmooth g)
    {F : M.Carrier → ComplexVector N} (hF : IsHolomorphicVecMap F) :
    SmoothFn (immersionDifferentialNormSq g F) := by
  intro x
  have hJ (a : Fin N) (b : Fin n) :
      ContDiffOn ℝ ∞ (fun z => immersionDerivativeMatrix F x z a b) (chartTarget x) :=
    (complex_holomorphic_contDiffOn (isOpen_extChartAt_target (I := ComplexModel n) x)
      (immersionDerivativeMatrix_differentiableOn hF x a b)).restrict_scalars ℝ
  have hI (b c : Fin n) : ContDiffOn ℝ ∞ (fun z => (hMat g x z)⁻¹ b c) (chartTarget x) :=
    entrywise_matrix_inv_contDiffOn
      (Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg x)
      (fun z hz => ne_of_gt (hMat_posDef g x z hz).det_pos) b c
  have hQ (a : Fin N) : ContDiffOn ℝ ∞ (fun z => dualNormMat (hMat g x z)
      (WithLp.toLp 2 (fun b => immersionDerivativeMatrix F x z a b))) (chartTarget x) := by
    change ContDiffOn ℝ ∞ (fun z =>
      (∑ b, star (immersionDerivativeMatrix F x z a b) *
        ∑ c, (hMat g x z)⁻¹ c b * immersionDerivativeMatrix F x z a c).re) (chartTarget x)
    exact Complex.reCLM.contDiff.comp_contDiffOn (ContDiffOn.sum fun b _ =>
      (Complex.conjCLE.contDiff.comp_contDiffOn (hJ a b)).mul
        (ContDiffOn.sum fun c _ => (hI c b).mul (hJ a c)))
  exact (ContDiffOn.sum fun a _ => hQ a).congr
    fun z hz => immersionDifferentialNormSq_in_fixed_chart g hF x hz

end Yau.NodeProofs.D02Aux
