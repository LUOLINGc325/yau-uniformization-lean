import Yau.Proofs.F01AffineMetricMatrix
import Yau.Proofs.F01QuadraticNormalJet
import Yau.Proofs.F01QuadraticLocalChart
import Yau.Proofs.F01QuadraticChartGram

/-! Genuine Kähler normal holomorphic coordinates. The quadratic coefficients
are computed from the original metric jet, and both coordinate directions
are smooth on their full open domains. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_normal_holomorphic_chart (g : SmoothMetric M) (k : HermitianField M)
    (p : M.Carrier) :
    ∃ e : OpenPartialHomeomorph (ComplexVector n) M.Carrier,
      e 0 = p ∧ (0 : ComplexVector n) ∈ e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source ∧
      ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target ∧
      L17Aux.pullbackMatrix g.form e 0 = 1 ∧
      (∀ i j l, wirt (fun z => L17Aux.pullbackMatrix g.form e z i j) 0 (stdVec l) = 0) ∧
      ∃ values : Fin n → ℝ,
        L17Aux.pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)) := by
  obtain ⟨A, hA, hG0, values, hK0⟩ := exists_normalizing_affine_metric g.form k p
  let e1 := affineChangedChart (ordinaryChart p) (chartPt p p) A hA
  let G := affineMetricMatrix g.form p A hA
  let K := affineMetricMatrix k p A hA
  have hsrc0 : (0 : ComplexVector n) ∈ e1.source :=
    affineChangedChart_zero_source (ordinaryChart p) (chartPt p p)
      (by rw [ordinaryChart_source]; exact mem_extChartAt_target p) A hA
  have hz0 : affineCoordinateHomeomorph (chartPt p p) A hA 0 ∈ chartTarget p := by
    rw [affineCoordinateHomeomorph_apply, map_zero, add_zero]
    exact mem_extChartAt_target p
  have he1 : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e1 e1.source :=
    affineChangedChart_contMDiffOn _ (ordinaryChart_contMDiffOn p) _ A hA
  have hei1 : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e1.symm e1.target :=
    affineChangedChart_inverse_contMDiffOn _ (ordinaryChart_inverse_contMDiffOn p) _ A hA
  have hcenter : e1 0 = p := by
    rw [affineChangedChart_center]
    rw [ordinaryChart_apply]
    exact (extChartAt (ComplexModel n) p).left_inv (mem_extChartAt_source p)
  have hGentry (i j : Fin n) : DifferentiableAt ℝ (fun z => G z i j) 0 :=
    affineMetricMatrix_entry_differentiableAt g.form (L12Aux.metricSmooth_of_smoothMetric g)
      p A hA hz0 i j
  have hsym (i j l : Fin n) : wirt (fun y => G y i j) 0 (stdVec l) =
      wirt (fun y => G y i l) 0 (stdVec j) := affineMetricMatrix_wirt_symm g p A hA hz0 i j l
  let B := normalCoordinateCorrection G
  obtain ⟨q, hq, hqsrc, hqzero, hqsmooth, hqismooth⟩ := quadraticCoordinate_smooth_local_chart B
  let e := q.trans e1
  have hesrc : (0 : ComplexVector n) ∈ e.source := chart_composition_zero_source e1 q hsrc0 hqsrc hqzero
  have hecenter : e 0 = p := by
    change e1 (q 0) = p
    rw [hqzero]
    exact hcenter
  have hGgerm : L17Aux.pullbackMatrix g.form e1 =ᶠ[𝓝 (0 : ComplexVector n)] G := by
    filter_upwards [e1.open_source.mem_nhds hsrc0] with z hz
    exact affineMetricMatrix_eq_pullback g.form p A hA hz
  have hKgerm : L17Aux.pullbackMatrix k e1 =ᶠ[𝓝 (0 : ComplexVector n)] K := by
    filter_upwards [e1.open_source.mem_nhds hsrc0] with z hz
    exact affineMetricMatrix_eq_pullback k p A hA hz
  have hnew := quadratic_chart_pullback_germ g.form e1 he1 hsrc0 B q hq hqsrc G hGgerm
  have hknew := quadratic_chart_pullback_germ k e1 he1 hsrc0 B q hq hqsrc K hKgerm
  have hgvalue : L17Aux.pullbackMatrix g.form e 0 = 1 := by
    have hv : L17Aux.pullbackMatrix g.form e 0 = G 0 := by
      simpa only [quadraticJacobian_zero, quadraticCoordinate_zero,
        Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using hnew.eq_of_nhds
    exact hv.trans hG0
  have hkvalue : L17Aux.pullbackMatrix k e 0 = Matrix.diagonal (fun i => (values i : ℂ)) := by
    have hv : L17Aux.pullbackMatrix k e 0 = K 0 := by
      simpa only [quadraticJacobian_zero, quadraticCoordinate_zero,
        Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using hknew.eq_of_nhds
    exact hv.trans hK0
  refine ⟨e, hecenter, hesrc, chart_composition_contMDiffOn e1 q he1 hqsmooth,
    chart_composition_inverse_contMDiffOn e1 q hei1 hqismooth, hgvalue, ?_, values, hkvalue⟩
  intro i j l
  have hentry : (fun z => L17Aux.pullbackMatrix g.form e z i j) =ᶠ[𝓝 (0 : ComplexVector n)]
      (fun z => ((quadraticJacobian B z)ᴴ * G (quadraticCoordinate B z) * quadraticJacobian B z) i j) := by
    filter_upwards [hnew] with z hz
    exact congrArg (fun H : Matrix (Fin n) (Fin n) ℂ => H i j) hz
  have hw : wirt (fun z => L17Aux.pullbackMatrix g.form e z i j) 0 (stdVec l) =
      wirt (fun z => ((quadraticJacobian B z)ᴴ * G (quadraticCoordinate B z) * quadraticJacobian B z) i j)
        0 (stdVec l) := by
    unfold wirt
    rw [hentry.fderiv_eq]
  exact hw.trans (quadratic_normal_jet_zero G hGentry hG0 hsym i j l)

end Yau.NodeProofs.F01Aux
