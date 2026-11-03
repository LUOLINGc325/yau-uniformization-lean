import Yau.Proofs.C04BoundedGeometryChartsParallelComplex

/-! The actual radial parallel frame intertwines the two complex structures. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem realParallelField_initial_coordinates (g : SmoothMetric M)
    (q : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    (w : TangentSpace 𝓘(ℝ, ComplexVector n) q.proj) :
    realTangentCoords q.proj (realGeodesicFlow g q 0).proj (realParallelField g q w 0) =
      realTangentCoords q.proj q.proj w := by
  have H := (realParallelField_totalSpace g q w 0).trans (realParallelLift_zero g q w)
  exact congrArg (fun z : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier =>
    realTangentCoords q.proj z.proj z.2) H

theorem parallelUnitaryFrame_initial_coordinates (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) :
    realTangentCoords p (realGeodesicFlow g (radialInitialState p U v) 0).proj
      (parallelUnitaryFrame g p U v 0 w) = realTangentCoords p p (realUnitaryFrame p U w) := by
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup g.form y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace g.form y
  let e₀ := realInitialOrthonormalFrame g p
  have hcol (i : Fin (2 * n)) :
      realTangentCoords p (realGeodesicFlow g (radialInitialState p U v) 0).proj
        (realParallelField g (radialInitialState p U v) (realInitialOrthonormalFrame g p i) 0) =
      realTangentCoords p p (realInitialOrthonormalFrame g p i) :=
    realParallelField_initial_coordinates g (radialInitialState p U v) _
  rw [parallelUnitaryFrame_expansion, map_sum]
  simp only [map_smul, hcol]
  change (∑ i, (e₀.repr (realUnitaryFrame p U w)) i • realTangentCoords p p (e₀ i)) = _
  have H := congrArg (realTangentCoords p p) (e₀.sum_repr (realUnitaryFrame p U w))
  simpa only [map_sum, map_smul] using H

theorem parallelUnitaryFrame_initial_complex (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) :
    parallelUnitaryFrame g p U v 0 (Complex.I • w) =
      realTangentJ (realGeodesicFlow g (radialInitialState p U v) 0).proj
        (parallelUnitaryFrame g p U v 0 w) := by
  let y := (realGeodesicFlow g (radialInitialState p U v) 0).proj
  have hy : y ∈ (chartAt (ComplexVector n) p).source := by
    simp only [y, realGeodesicFlow_zero, radialInitialState]
    exact mem_chart_source _ _
  have hinj : Function.Injective (realTangentCoords p y) :=
    (show Function.LeftInverse (realFrameCLM p y) (realTangentCoords p y) from
      fun V => realFrameCLM_realTangentCoords p y hy V).injective
  apply hinj
  rw [parallelUnitaryFrame_initial_coordinates, realTangentJ_eq_accepted,
    Yau.NodeProofs.P02Aux.realTangentCoords_realTangentJ p y hy,
    parallelUnitaryFrame_initial_coordinates]
  have H := congrArg (realTangentCoords p p) (realUnitaryFrame_intertwines p U w)
  rw [realTangentJ_eq_accepted,
    Yau.NodeProofs.P02Aux.realTangentCoords_realTangentJ p p (mem_chart_source _ _)] at H
  exact H.symm

theorem radialParallelFrame_intertwines (g : SmoothMetric M) (hk : KahlerClosed g.form)
    (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) :
    radialParallelFrame g p U v (Complex.I • w) =
      realTangentJ (unitaryExponential g p U v) (radialParallelFrame g p U v w) := by
  let q := radialInitialState p U v
  let γ := fun s => (realGeodesicFlow g q s).proj
  have hγ := Yau.NodeProofs.P02Aux.realGeodesicFlow_fieldGeodesicOn g q (Set.Ioo (-1) (1 + 1))
  have H := parallel_frame_complex_of_initial g.form (metricSmooth_of_smoothMetric g) hk γ
    1 (by norm_num) hγ (parallelUnitaryFrame g p U v)
    (parallelUnitaryFrame_initial_complex g p U v) (by
      intro t ht w
      have hvel : (geoChartState γ (γ t) t).2 =
          realTangentCoords (γ t) (γ t) (realGeodesicFlow g q t).2 :=
        (realGeodesicFlow_baseCoords_hasDerivAt g q t).deriv
      rw [hvel]
      exact parallelUnitaryFrame_coordinates_hasDerivAt g p U v w t)
    1 (by norm_num) w
  simpa only [parallelUnitaryFrame_one, γ, q, unitaryExponential, realExponentialMap,
    radialInitialState] using H

end Yau.Proofs.C04ChartsAux
