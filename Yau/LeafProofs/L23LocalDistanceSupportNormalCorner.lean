import Yau.LeafProofs.L23LocalDistanceSupportVertexStationary
import Yau.LeafProofs.L23FieldMetricVertexFirstVariation
import Yau.LeafProofs.L23FieldMetricNormalBranchCurve

/-! Adjacent actual normal branches of a globally minimizing polygon have identical vertex phases. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n N : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem fieldPolygon_no_corner_at_normal_branches
    (h : HermitianField M) (hh : MetricSmooth h) (O : Set M.Carrier)
    (q y : M.Carrier) (v : Fin N → M.Carrier)
    (hmin : ∀ w : Fin N → M.Carrier, fieldPolygonEnergy h q y v ≤ fieldPolygonEnergy h q y w)
    (j : Fin N) (cLeft cRight : M.Carrier)
    (BLeft BRight : Set (ComplexVector n)) (ρLeft εLeft ρRight εRight : ℝ)
    (XLeft XRight : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (eLeft eRight : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (HLeft : FieldNormalEndpointData h cLeft O BLeft ρLeft εLeft XLeft eLeft)
    (HRight : FieldNormalEndpointData h cRight O BRight ρRight εRight XRight eRight)
    (hLeftStart : fieldPolygonPoint q y v j.castSucc.castSucc ∈ (chartAt (ComplexVector n) cLeft).source)
    (hLeftEnd : v j ∈ (chartAt (ComplexVector n) cLeft).source)
    (hRightStart : v j ∈ (chartAt (ComplexVector n) cRight).source)
    (hRightEnd : fieldPolygonPoint q y v j.succ.succ ∈ (chartAt (ComplexVector n) cRight).source)
    (hPairLeft : (chartPt cLeft (fieldPolygonPoint q y v j.castSucc.castSucc),chartPt cLeft (v j)) ∈ eLeft.target)
    (hPairRight : (chartPt cRight (v j),chartPt cRight (fieldPolygonPoint q y v j.succ.succ)) ∈ eRight.target) :
    geoChartState (fieldNormalBranchCurve cLeft XLeft eLeft
      (fieldPolygonPoint q y v j.castSucc.castSucc) (v j)) (v j) 1 =
    geoChartState (fieldNormalBranchCurve cRight XRight eRight
      (v j) (fieldPolygonPoint q y v j.succ.succ)) (v j) 0 := by
  let uLeft := fderiv ℝ (realChartChange cLeft (v j)) (chartPt cLeft (v j))
    (normalFamilyPhase XLeft (eLeft.symm
      (chartPt cLeft (fieldPolygonPoint q y v j.castSucc.castSucc),chartPt cLeft (v j))) 1).2
  let uRight := fderiv ℝ (realChartChange cRight (v j)) (chartPt cRight (v j))
    (eRight.symm (chartPt cRight (v j),chartPt cRight (fieldPolygonPoint q y v j.succ.succ))).2
  have hnode : v j ∈ (chartAt (ComplexVector n) (v j)).source := mem_chart_source _ _
  have Hvel : uLeft = uRight := by
    apply fieldPolygon_minimizer_no_corner_of_variations h q y v hmin j (v j) hnode uLeft uRight
    intro w
    refine ⟨fieldVertexCurve (v j) (v j) w,fieldVertexCurve_zero _ _ hnode w,?_,?_⟩
    · exact fieldNormalBranch_terminal_firstVariation h hh cLeft O BLeft ρLeft εLeft XLeft eLeft HLeft
        (fieldPolygonPoint q y v j.castSucc.castSucc) (v j) (v j) hLeftStart hLeftEnd hPairLeft hnode w
    · exact fieldNormalBranch_initial_firstVariation h hh cRight O BRight ρRight εRight XRight eRight HRight
        (v j) (fieldPolygonPoint q y v j.succ.succ) (v j) hRightStart hRightEnd hPairRight hnode w
  rw [fieldNormalBranchCurve_terminal_state h cLeft (v j) O BLeft ρLeft εLeft XLeft eLeft HLeft
      _ _ hLeftStart hLeftEnd hPairLeft hnode,
    fieldNormalBranchCurve_initial_state h cRight (v j) O BRight ρRight εRight XRight eRight HRight
      _ _ hRightStart hRightEnd hPairRight hnode]
  exact Prod.ext rfl Hvel

end Yau.LeafProofs.L23Aux
