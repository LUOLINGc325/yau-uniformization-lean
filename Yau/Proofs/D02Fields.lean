import Yau.Proofs.D02CotangentExtrema

/-! Actual evaluation of cotangent vectors on global holomorphic tangent fields. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Bundle

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

set_option maxHeartbeats 800000

variable {n m : ℕ} {M : ComplexManifold n}

/-- Coordinates of a genuine holomorphic tangent section are continuous. -/
theorem fieldCoords_continuousOn {V : VectorField M} (hV : IsHolomorphicField V)
    (x : M.Carrier) : ContinuousOn (fieldCoords V x) (chartTarget x) := by
  let e := trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) x
  have hbase : ContinuousOn (chartInv x) (chartTarget x) :=
    continuousOn_extChartAt_symm x
  have hsection : ContinuousOn
      (fun z => (⟨chartInv x z, V (chartInv x z)⟩ : TangentBundle (ComplexModel n) M.Carrier))
      (chartTarget x) := hV.continuous.comp_continuousOn hbase
  have hmap : Set.MapsTo
      (fun z => (⟨chartInv x z, V (chartInv x z)⟩ : TangentBundle (ComplexModel n) M.Carrier))
      (chartTarget x) e.source := by
    intro z hz
    rw [Trivialization.mem_source]
    change chartInv x z ∈ (chartAt (ComplexVector n) x).source
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have he := (e.continuousOn.comp hsection hmap).snd
  apply he.congr
  intro z hz
  change tangentCoords x (chartInv x z) (V (chartInv x z)) =
    tangentCoordChange (ComplexModel n) (chartInv x z) x (chartInv x z) (V (chartInv x z))
  exact tangentCoords_eq_coordChange x (chartInv x z)
    ((extChartAt (ComplexModel n) x).map_target hz) _

/-- The intrinsic scalar evaluation used throughout the cotangent argument. -/
def fieldEvaluation (V : VectorField M) (y : CotangentPoint M) : ℂ := y.2 (V y.1)

/-- In a valid induced chart, evaluation is the unconjugated coordinate pairing. -/
theorem fieldEvaluation_chart (V : VectorField M) (x : M.Carrier)
    {p : CotangentCoord n} (hp : p ∈ cotangentTarget x) :
    fieldEvaluation V (cotangentChartInv x p) =
      ∑ i, (fieldCoords V x p.1) i * p.2 i := by
  let y := chartInv x p.1
  have hy : y ∈ (extChartAt (ComplexModel n) x).source :=
    (extChartAt (ComplexModel n) x).map_target hp.1
  have h := covector_apply_chartVec x y (covectorOfCoords x y p.2)
    (tangentCoords x y (V y))
  have he : chartVec x y (tangentCoords x y (V y)) = V y :=
    chartVec_tangentCoords x y hy (V y)
  rw [he, covectorCoords_ofCoords x y hy p.2] at h
  exact h

/-- Evaluation is continuous in the actual atlas, with no product topology assumption. -/
theorem fieldEvaluation_continuousOn_chart {V : VectorField M} (hV : IsHolomorphicField V)
    (x : M.Carrier) :
    ContinuousOn (fun p => fieldEvaluation V (cotangentChartInv x p)) (cotangentTarget x) := by
  have hc : ContinuousOn (fun p : CotangentCoord n => fieldCoords V x p.1)
      (cotangentTarget x) := (fieldCoords_continuousOn hV x).comp continuous_fst.continuousOn
    (fun p hp => hp.1)
  have hsum : ContinuousOn
      (fun p : CotangentCoord n => ∑ i, fieldCoords V x p.1 i * p.2 i) (cotangentTarget x) :=
    continuousOn_finsetSum Finset.univ fun i _ =>
      ((EuclideanSpace.proj i).continuous.comp_continuousOn hc).mul
        (((EuclideanSpace.proj i).continuous.comp continuous_snd).continuousOn)
  exact hsum.congr fun p hp => fieldEvaluation_chart V x hp

/-- Squared Euclidean size of the same finite list of scalar evaluations. -/
def fieldEvaluationSq (V : Fin m → VectorField M) (y : CotangentPoint M) : ℝ :=
  ∑ i, ‖fieldEvaluation (V i) y‖ ^ 2

theorem fieldEvaluationSq_continuousOn_chart {V : Fin m → VectorField M}
    (hV : ∀ i, IsHolomorphicField (V i)) (x : M.Carrier) :
    ContinuousOn (fun p => fieldEvaluationSq V (cotangentChartInv x p)) (cotangentTarget x) := by
  exact continuousOn_finsetSum Finset.univ fun i _ =>
    ((fieldEvaluation_continuousOn_chart (hV i) x).norm).pow 2

/-- Pointwise spanning makes evaluation injective on each actual cotangent fibre. -/
theorem exists_fieldEvaluation_ne_zero {V : Fin m → VectorField M}
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i => V i x) = ⊤)
    {x : M.Carrier} {ξ : Covector n} (hξ : ξ ≠ 0) :
    ∃ i, fieldEvaluation (V i) (x, ξ) ≠ 0 := by
  by_contra h
  push Not at h
  have hle : Submodule.span ℂ (Set.range fun i => V i x) ≤ ξ.ker := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact h i
  apply hξ
  ext v
  have hv : v ∈ Submodule.span ℂ (Set.range fun i => V i x) := by
    rw [hspan x]
    trivial
  exact hle hv

theorem fieldEvaluationSq_pos {V : Fin m → VectorField M}
    (hspan : ∀ x, Submodule.span ℂ (Set.range fun i => V i x) = ⊤)
    {x : M.Carrier} {ξ : Covector n} (hξ : ξ ≠ 0) :
    0 < fieldEvaluationSq V (x, ξ) := by
  obtain ⟨i, hi⟩ := exists_fieldEvaluation_ne_zero hspan hξ
  have hi' : ‖fieldEvaluation (V i) (x, ξ)‖ ^ 2 ≤
      ∑ j : Fin m, ‖fieldEvaluation (V j) (x, ξ)‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖fieldEvaluation (V j) (x, ξ)‖)
      (Finset.mem_univ i)
  exact (sq_pos_of_pos (norm_pos_iff.mpr hi)).trans_le hi'

end Yau.NodeProofs.D02Aux
