import Yau.Proofs.C03FlatCompleteField

/-! The actual determinant volume of the half-flat Hermitian field. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ENNReal
open MeasureTheory Filter
namespace Yau.Proofs.C03Aux.FlatComplete
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false

theorem euclidean_chartPt (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier) :
    chartPt x = (fun y : ComplexVector n => y) := by
  funext y
  change extChartAt (ComplexModel n) (x : ComplexVector n) y = y
  rw [extChartAt_model_space_eq_id]
  rfl

theorem euclidean_hMat (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier) (z : ComplexVector n) :
    hMat (euclideanHermitianField n hn) x z =
      ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext a b
  unfold hMat
  rw [chartVec_euclidean, chartVec_euclidean, euclideanHermitianField_apply]
  change ((1 / 2 : ℝ) : ℂ) * inner ℂ (stdVec a) (stdVec b) = _
  by_cases hab : a = b <;>
    simp [stdVec, EuclideanSpace.inner_single_left, EuclideanSpace.single,
      Matrix.smul_apply, hab]

theorem euclidean_gMat (n : ℕ) (hn : 1 ≤ n)
    (x : (ComplexEuclideanManifold n hn).Carrier) :
    gMat (euclideanHermitianField n hn) x =
      ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
  euclidean_hMat n hn x _

/-- Standard Euclidean volume transported through the identity carrier map. -/
def euclideanVolume (n : ℕ) (hn : 1 ≤ n) :
    Measure (ComplexEuclideanManifold n hn).Carrier :=
  Measure.map (fun z : ComplexVector n =>
    (z : (ComplexEuclideanManifold n hn).Carrier)) volume

theorem euclideanVolume_apply (n : ℕ) (hn : 1 ≤ n)
    (s : Set (ComplexEuclideanManifold n hn).Carrier) (hs : MeasurableSet s) :
    euclideanVolume n hn s = (volume : Measure (ComplexVector n)) s := by
  have hc : Continuous (X := ComplexVector n) (Y := (ComplexEuclideanManifold n hn).Carrier)
      (fun z : ComplexVector n => (z : (ComplexEuclideanManifold n hn).Carrier)) := continuous_id
  have hm : Measurable (α := ComplexVector n) (β := (ComplexEuclideanManifold n hn).Carrier)
      (fun z : ComplexVector n =>
      (z : (ComplexEuclideanManifold n hn).Carrier)) := hc.measurable
  exact Measure.map_apply (α := ComplexVector n)
    (β := (ComplexEuclideanManifold n hn).Carrier) (μ := volume) hm hs

theorem euclidean_isRiemannianVolume (n : ℕ) (hn : 1 ≤ n) :
    IsRiemannianVolume (euclideanHermitianField n hn)
      (euclideanVolume n hn) := by
  intro x s hs hsource
  simp_rw [euclidean_realMetricFn_eq_one, Matrix.det_one, Real.sqrt_one,
    ENNReal.ofReal_one]
  have himage : chartPt x '' s = (s : Set (ComplexVector n)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (congrFun (euclidean_chartPt n hn x) z).symm ▸ hz
    · intro hy
      exact ⟨y, hy, congrFun (euclidean_chartPt n hn x) y⟩
  rw [himage, lebesgueC_eq_volume]
  simpa using euclideanVolume_apply n hn s hs

end Yau.Proofs.C03Aux.FlatComplete
