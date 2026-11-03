import Yau.LeafProofs.L23LocalDistanceSupportVertexVariation

/-! Global finite polygon minimality makes every free vertex first variation vanish. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n N : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem fieldPolygonEnergy_update_stationary
    (h : HermitianField M) (q y : M.Carrier) (v : Fin N → M.Carrier)
    (hmin : ∀ w : Fin N → M.Carrier, fieldPolygonEnergy h q y v ≤ fieldPolygonEnergy h q y w)
    (j : Fin N) (β : ℝ → M.Carrier) (hβ : β 0 = v j) {L R : ℝ}
    (hleft : HasDerivAt (fun r => inducedDistance h
      (fieldPolygonPoint q y v j.castSucc.castSucc) (β r)^2) L 0)
    (hright : HasDerivAt (fun r => inducedDistance h
      (β r) (fieldPolygonPoint q y v j.succ.succ)^2) R 0) : L+R = 0 := by
  have HD := fieldPolygonEnergy_update_hasDerivAt h q y v j β hleft hright
  have HM : IsLocalMin (fun r => fieldPolygonEnergy h q y (Function.update v j (β r))) 0 := by
    apply Eventually.of_forall
    intro r
    simp only [hβ,Function.update_eq_self]
    exact hmin _
  have Hzero := HD.deriv.symm.trans HM.deriv_eq_zero
  have Hpos : (0 : ℝ) < (N+1 : ℕ) := by positivity
  exact (mul_eq_zero.mp Hzero).resolve_left Hpos.ne'

theorem fieldPolygon_minimizer_no_corner_of_variations
    (h : HermitianField M) (q y : M.Carrier) (v : Fin N → M.Carrier)
    (hmin : ∀ w : Fin N → M.Carrier, fieldPolygonEnergy h q y v ≤ fieldPolygonEnergy h q y w)
    (j : Fin N) (c : M.Carrier) (hnode : v j ∈ (chartAt (ComplexVector n) c).source)
    (uLeft uRight : ComplexVector n)
    (hvariation : ∀ w : ComplexVector n, ∃ β : ℝ → M.Carrier, β 0 = v j ∧
      HasDerivAt (fun r => inducedDistance h
        (fieldPolygonPoint q y v j.castSucc.castSucc) (β r)^2)
          (2*realMetricInChart h c (chartPt c (v j)) uLeft w) 0 ∧
      HasDerivAt (fun r => inducedDistance h
        (β r) (fieldPolygonPoint q y v j.succ.succ)^2)
          (-2*realMetricInChart h c (chartPt c (v j)) uRight w) 0) : uLeft = uRight := by
  apply realMetricInChart_pairings_injective h c (v j) hnode
  intro w
  obtain ⟨β,hβ,hleft,hright⟩ := hvariation w
  have H := fieldPolygonEnergy_update_stationary h q y v hmin j β hβ hleft hright
  linarith

end Yau.LeafProofs.L23Aux
