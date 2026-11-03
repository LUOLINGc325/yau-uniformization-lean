import Yau.LeafProofs.L14BundleCurvature
import Yau.LeafProofs.L14CoefficientTransitions
import Yau.LeafProofs.L14CurvatureAlgebra

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem curvatureEnergy_pullback_algebra {n r : ℕ}
    (G J : Matrix (Fin n) (Fin n) ℂ) (A C : Matrix (Fin r) (Fin r) ℂ)
    (F : Matrix (Fin n) (Fin r) ℂ) (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (hJ : IsUnit J.det) (hAC : A * C = 1) :
    ((Jᴴ * G * J).det.re)⁻¹ *
      nakanoQuadratic (fun i j => Aᴴ * (∑ p, ∑ q, (J p i * star (J q j)) • R p q) * A)
        ((Jᴴ * G * J)⁻¹ * (J.det • (Jᴴ * F * Cᵀ))) =
      (G.det.re)⁻¹ * nakanoQuadratic R (G⁻¹ * F) := by
  rw [nakanoQuadratic_pullback, raised_coefficients_change G J A C F hJ hAC]
  have hscale : nakanoQuadratic R (J.det • (G⁻¹ * F)) =
      Complex.normSq J.det * nakanoQuadratic R (G⁻¹ * F) :=
    nakanoQuadratic_smul R (fun i α => (G⁻¹ * F) i α) J.det
  rw [hscale, matrix_det_congruence_re]
  have hδ : Complex.normSq J.det ≠ 0 := by
    intro hzero
    exact hJ.ne_zero (Complex.normSq_eq_zero.mp hzero)
  rw [mul_inv_rev]
  calc
    _ = (G.det.re)⁻¹ * ((Complex.normSq J.det)⁻¹ * Complex.normSq J.det) *
        nakanoQuadratic R (G⁻¹ * F) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hδ, mul_one]

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def chartCurvatureEnergy (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (u : NQForm E 1) (a : M.Carrier) (z : ComplexVector n) : ℝ :=
  ((hMat g a z).det.re)⁻¹ * nakanoQuadratic (weightedCurvature (r := r) E h φ a z)
    ((hMat g a z)⁻¹ * oneCoefficientsMatrix (r := r) E u a z)

theorem chartCurvatureEnergy_overlap (hE : Holomorphic (r := r) E)
    (g : HermitianField M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1)
    (a b : M.Carrier) (z : ComplexVector n) (hz : z ∈ bundleChartOverlap (r := r) E a b) :
    chartCurvatureEnergy (r := r) E g h φ u b z =
      chartCurvatureEnergy (r := r) E g h φ u a (chartPt a (chartInv b z)) := by
  classical
  let T := fun w => chartPt a (chartInv b w)
  let J := Matrix.of fun p i => fderiv ℂ T z (stdVec i) p
  let G := hMat g a (T z)
  let A := bundleFrameTransitionMatrix (r := r) E b a (chartInv b z)
  let C := bundleFrameTransitionMatrix (r := r) E a b (chartInv b z)
  let F := oneCoefficientsMatrix (r := r) E u a (T z)
  let R := weightedCurvature (r := r) E h φ a (T z)
  have hG : hMat g b z = Jᴴ * G * J := hMat_overlap E g a b z hz
  have hF : oneCoefficientsMatrix (r := r) E u b z = J.det • (Jᴴ * F * Cᵀ) :=
    coefficients_one_overlap_matrix E u a b z hz
  have hR : weightedCurvature (r := r) E h φ b z =
      (fun i j => Aᴴ * (∑ p, ∑ q, (J p i * star (J q j)) • R p q) * A) := by
    funext i j
    exact weightedCurvature_overlap E hE h hh φ hφ a b z hz i j
  have hAC : A * C = 1 :=
    bundleFrameTransitionMatrix_mul_reverse E b a (chartInv b z) hz.1.2 hz.2.2
  have hJ : IsUnit J.det := by
    let y := chartInv b z
    let ba := chartFrameBasis a y hz.2.1
    let bb := chartFrameBasis b y ((extChartAt (ComplexModel n) b).map_target hz.1.1)
    have he : ba.toMatrix bb = J := chartFrameBasis_toMatrix_fderiv a b z hz.1.1 hz.2.1
    rw [← he]
    exact ba.isUnit_det bb
  unfold chartCurvatureEnergy
  rw [hG, hF, hR]
  exact curvatureEnergy_pullback_algebra G J A C F R hJ hAC

theorem curvatureEnergy_eq_chartCurvatureEnergy (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1) (x : M.Carrier) :
    curvatureEnergy (r := r) E g h φ x
      (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α) =
        chartCurvatureEnergy (r := r) E g h φ u x (chartPt x x) := by
  unfold curvatureEnergy chartCurvatureEnergy
  rw [gMat_inv_det_re]
  rfl

theorem curvatureEnergy_inChart (hE : Holomorphic (r := r) E)
    (g : HermitianField M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    let x := chartInv a z
    curvatureEnergy (r := r) E g h φ x
      (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α) =
        ((hMat g a z).det.re)⁻¹ * nakanoQuadratic (weightedCurvature (r := r) E h φ a z)
          (fun i α => ∑ j, (hMat g a z)⁻¹ i j * coefficients (r := r) E u a z (fun _ => j) α) := by
  let x := chartInv a z
  have hxx : chartInv x (chartPt x x) = x := chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hself : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [hxx]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hoverlap : chartPt x x ∈ bundleChartOverlap (r := r) E a x := by
    refine ⟨hself, ?_⟩
    change chartInv x (chartPt x x) ∈ bundleChartSource (r := r) E a
    rw [hxx]
    exact ⟨(extChartAt (ComplexModel n) a).map_target hz.1, hz.2⟩
  have hzback : chartPt a (chartInv x (chartPt x x)) = z := by
    rw [hxx]
    exact (extChartAt (ComplexModel n) a).right_inv hz.1
  calc
    _ = chartCurvatureEnergy (r := r) E g h φ u x (chartPt x x) :=
      curvatureEnergy_eq_chartCurvatureEnergy E g h φ u x
    _ = chartCurvatureEnergy (r := r) E g h φ u a (chartPt a (chartInv x (chartPt x x))) :=
      chartCurvatureEnergy_overlap E hE g h hh φ hφ u a x (chartPt x x) hoverlap
    _ = chartCurvatureEnergy (r := r) E g h φ u a z := congrArg (chartCurvatureEnergy (r := r) E g h φ u a) hzback
    _ = _ := rfl

end Yau.LeafProofs.L14Aux
