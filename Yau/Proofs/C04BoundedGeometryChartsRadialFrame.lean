import Yau.Proofs.C04BoundedGeometryChartsPairing
import Yau.Proofs.C04BoundedGeometryChartsTransportRegularity

/-! The actual radial parallel frame, built from transported orthonormal bases. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def radialInitialState (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨p, realUnitaryFrame p U v⟩

def radialParallelFrame (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (unitaryExponential g p U v) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let e₀ := realInitialOrthonormalFrame g p
  let e := realParallelFrame g (radialInitialState p U v) e₀ 1
  exact ((realUnitaryFrame p U).trans e₀.repr.toContinuousLinearEquiv).trans
    e.repr.symm.toContinuousLinearEquiv

theorem radialParallelFrame_pairing (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v a b : ComplexVector n) :
    (underlyingRealRiemannianMetric g.form).inner (unitaryExponential g p U v)
      (radialParallelFrame g p U v a) (radialParallelFrame g p U v b) =
      (underlyingRealRiemannianMetric g.form).inner p
        (realUnitaryFrame p U a) (realUnitaryFrame p U b) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let e₀ := realInitialOrthonormalFrame g p
  let e := realParallelFrame g (radialInitialState p U v) e₀ 1
  change ⟪e.repr.symm (e₀.repr (realUnitaryFrame p U a)),
      e.repr.symm (e₀.repr (realUnitaryFrame p U b))⟫_ℝ =
    ⟪realUnitaryFrame p U a, realUnitaryFrame p U b⟫_ℝ
  rw [e.repr.symm.inner_map_map, e₀.repr.inner_map_map]

theorem radialParallelFrame_metric (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p)
    (hU : ∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
      (1 : Matrix (Fin n) (Fin n) ℂ) i j) (v a b : ComplexVector n) :
    (underlyingRealRiemannianMetric g.form).inner (unitaryExponential g p U v)
      (radialParallelFrame g p U v a) (radialParallelFrame g p U v b) =
      2 * (⟪a, b⟫_ℂ).re := by
  rw [radialParallelFrame_pairing, realUnitaryFrame_pairing, unitary_frame_pairing g.form p U hU]

/-- Coframe of the actual real exponential differential in its radial frame. -/
def radialCoframe (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n :=
  (radialParallelFrame g p U v).symm.toContinuousLinearMap.comp
    (realMapDeriv (unitaryExponential g p U) v)

end Yau.Proofs.C04ChartsAux
