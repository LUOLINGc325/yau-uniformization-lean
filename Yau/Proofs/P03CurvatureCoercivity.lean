import Yau.Proofs.P03CurvatureMetricContraction
import Yau.Proofs.P03NakanoRelativeAlgebra

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The actual weighted curvature controls the coefficient norm whenever
the actual Levi matrix dominates a multiple of the actual base metric. -/
theorem curvatureEnergy_coercive_of_levi (g : HermitianField M)
    (h : Metric (M := M) E) (hN : NakanoNonnegative (r := r) E h)
    (φ : M.Carrier → ℝ) (x : M.Carrier) (lam : ℝ)
    (hLG : (leviC (inChart x φ) (chartPt x x) - (lam : ℂ) • gMat g x).PosSemidef)
    (V : Fin n → Fin r → ℂ) :
    lam * (coefficientInner (r := r) E g h x V V).re ≤
      curvatureEnergy (r := r) E g h φ x V := by
  let U : Fin n → Fin r → ℂ := fun i α => ∑ j, (gMat g x)⁻¹ i j * V j α
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hc := nakano_leviCorrection_relative_lower
    (leviC (inChart x φ) (chartPt x x)) (gMat g x)
    (BundleDbar.metricMatrix (r := r) E h x (chartPt x x)) lam hLG
    (metricMatrix_posDef E h x (chartPt x x) hz).posSemidef U
  have hR := hN x (chartPt x x) hz U
  have hs : lam * nakanoQuadratic
      (fun i j => gMat g x j i • BundleDbar.metricMatrix (r := r) E h x (chartPt x x)) U ≤
      nakanoQuadratic (weightedCurvature (r := r) E h φ x (chartPt x x)) U := by
    unfold weightedCurvature
    rw [nakanoQuadratic_add]
    linarith
  have hd : 0 ≤ (gMat g x)⁻¹.det.re :=
    (Complex.nonneg_iff.mp (gMat_posDef g x).inv.posSemidef.det_nonneg).1
  calc
    lam * (coefficientInner (r := r) E g h x V V).re = (gMat g x)⁻¹.det.re *
        (lam * nakanoQuadratic (fun i j => gMat g x j i •
          BundleDbar.metricMatrix (r := r) E h x (chartPt x x)) U) := by
      rw [← raised_metric_nakano_eq_coefficientInner E g h x V]
      ring
    _ ≤ (gMat g x)⁻¹.det.re *
        nakanoQuadratic (weightedCurvature (r := r) E h φ x (chartPt x x)) U :=
      mul_le_mul_of_nonneg_left hs hd
    _ = curvatureEnergy (r := r) E g h φ x V := rfl

end Yau.NodeProofs.P03Aux
