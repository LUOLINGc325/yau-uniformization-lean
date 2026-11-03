import Yau.Proofs.C04BoundedGeometryChartsRadialFrame

/-! The actual parallel frame at every time of the radial geodesic. -/

noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def parallelUnitaryFrame (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) (t : ℝ) :
    ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (realGeodesicFlow g (radialInitialState p U v) t).proj := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let e₀ := realInitialOrthonormalFrame g p
  let e := realParallelFrame g (radialInitialState p U v) e₀ t
  exact ((realUnitaryFrame p U).trans e₀.repr.toContinuousLinearEquiv).trans
    e.repr.symm.toContinuousLinearEquiv

@[simp] theorem parallelUnitaryFrame_one (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    parallelUnitaryFrame g p U v 1 = radialParallelFrame g p U v := rfl

theorem parallelUnitaryFrame_expansion (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) (t : ℝ) :
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup g.form y
    letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentInnerProductSpace g.form y
    parallelUnitaryFrame g p U v t w =
      ∑ i : Fin (2 * n),
        ((realInitialOrthonormalFrame g p).repr (realUnitaryFrame p U w)) i •
          realParallelField g (radialInitialState p U v) (realInitialOrthonormalFrame g p i) t := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let e₀ := realInitialOrthonormalFrame g p
  let e := realParallelFrame g (radialInitialState p U v) e₀ t
  change e.repr.symm (e₀.repr (realUnitaryFrame p U w)) = _
  calc
    _ = ∑ i, (e₀.repr (realUnitaryFrame p U w)) i • e i :=
      (e.sum_repr_symm _).symm
    _ = _ := by simp only [e, e₀, realParallelFrame_apply] <;> rfl

theorem parallelUnitaryFrame_coordinates_hasDerivAt (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) (t : ℝ) :
    letI := manifold_realSmooth M
    let γ := fun s => (realGeodesicFlow g (radialInitialState p U v) s).proj
    HasDerivAt (fun s => realTangentCoords (γ t) (γ s) (parallelUnitaryFrame g p U v s w))
      (-chartChristoffelBilin g.form (γ t) (chartPt (γ t) (γ t))
        (realTangentCoords (γ t) (γ t) (realGeodesicFlow g (radialInitialState p U v) t).2)
        (realTangentCoords (γ t) (γ t) (parallelUnitaryFrame g p U v t w))) t := by
  letI := manifold_realSmooth M
  letI := manifold_realPhase M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let q := radialInitialState p U v
  let c := (realGeodesicFlow g q t).proj
  let e₀ := realInitialOrthonormalFrame g p
  let α := fun i : Fin (2 * n) => (e₀.repr (realUnitaryFrame p U w)) i
  let Γ := chartChristoffelBilin g.form c (chartPt c c)
    (realTangentCoords c c (realGeodesicFlow g q t).2)
  have hcol (i : Fin (2 * n)) := realParallelField_coords_hasDerivAt g q (e₀ i) t
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hcol i).const_smul (α i))
  have hcoord (s : ℝ) :
      realTangentCoords c (realGeodesicFlow g q s).proj (parallelUnitaryFrame g p U v s w) =
        ∑ i, α i • realTangentCoords c (realGeodesicFlow g q s).proj
          (realParallelField g q (e₀ i) s) := by
    rw [parallelUnitaryFrame_expansion]
    simp only [map_sum, map_smul, α, e₀, q]
  have hD : (∑ i, α i • (-Γ (realTangentCoords c c (realParallelField g q (e₀ i) t)))) =
      -Γ (realTangentCoords c c (parallelUnitaryFrame g p U v t w)) := by
    rw [hcoord]
    simp only [map_sum, map_smul, smul_neg, Finset.sum_neg_distrib] <;> rfl
  change HasDerivAt (fun s => ∑ i, α i • realTangentCoords c
      (realGeodesicFlow g q s).proj (realParallelField g q (e₀ i) s))
    (∑ i, α i • (-Γ (realTangentCoords c c (realParallelField g q (e₀ i) t)))) t at hsum
  rw [hD] at hsum
  exact hsum.congr_of_eventuallyEq (Eventually.of_forall hcoord)

end Yau.Proofs.C04ChartsAux
