import Yau.LeafProofs.L23LocalDistanceSupportNormalEdges
import Yau.LeafProofs.L23FieldMetricNormalBranchLength
import Yau.LeafProofs.L23FieldMetricCompactBranches

/-! The actual short normal edges of a globally minimizing polygon have matching phases. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n N : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem exists_normal_polygon_edges_matching_phase_length
    (h : HermitianField M) (hh : MetricSmooth h) (O : Set M.Carrier)
    (q y : M.Carrier) (v : Fin N → M.Carrier)
    (hmin : ∀ w : Fin N → M.Carrier, fieldPolygonEnergy h q y v ≤ fieldPolygonEnergy h q y w)
    (hbranches : ∀ i : Fin (N+1), HasFieldNormalBranch h O
      (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ)) :
    ∃ (ε : Fin (N+1) → ℝ) (γ : Fin (N+1) → ℝ → M.Carrier),
      (∀ i, 0 < ε i ∧ γ i 0 = fieldPolygonPoint q y v i.castSucc ∧
        γ i 1 = fieldPolygonPoint q y v i.succ ∧
        FieldGeodesicOn h (γ i) (Set.Ioo (-ε i) (1+ε i)) ∧
        Set.MapsTo (γ i) (Set.Icc (0 : ℝ) 1) O ∧
        fieldPathELength h (γ i) 0 1 = ENNReal.ofReal (inducedDistance h
          (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ))) ∧
      ∀ j : Fin N, geoChartState (γ j.castSucc) (v j) 1 = geoChartState (γ j.succ) (v j) 0 := by
  classical
  have hex : ∀ i : Fin (N+1), ∃ (c : M.Carrier) (B : Set (ComplexVector n)) (ρ ε : ℝ)
      (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
      (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n)),
      FieldNormalEndpointData h c O B ρ ε X e ∧
        fieldPolygonPoint q y v i.castSucc ∈ (chartAt (ComplexVector n) c).source ∧
        fieldPolygonPoint q y v i.succ ∈ (chartAt (ComplexVector n) c).source ∧
        (chartPt c (fieldPolygonPoint q y v i.castSucc),chartPt c (fieldPolygonPoint q y v i.succ)) ∈ e.target := hbranches
  choose c B ρ ε X e H hsrc₀ hsrc₁ hpair using hex
  let γ : Fin (N+1) → ℝ → M.Carrier := fun i => fieldNormalBranchCurve (c i) (X i) (e i)
    (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ)
  refine ⟨ε,γ,?_,?_⟩
  · intro i
    have Hcurve := fieldNormalBranchCurve_data h (c i) O (B i) (ρ i) (ε i) (X i) (e i) (H i)
      _ _ (hsrc₀ i) (hsrc₁ i) (hpair i)
    exact ⟨(H i).2.2.2.2.1,Hcurve.1,Hcurve.2.1,Hcurve.2.2.1,Hcurve.2.2.2,
      fieldNormalBranchCurve_pathELength h hh (c i) O (B i) (ρ i) (ε i) (X i) (e i) (H i)
        _ _ (hsrc₀ i) (hsrc₁ i) (hpair i)⟩
  · intro j
    have HnodeLeft : fieldPolygonPoint q y v j.castSucc.succ = v j := fieldPolygonPoint_interior q y v j
    have HnodeRight : fieldPolygonPoint q y v j.succ.castSucc = v j := by
      have Hidx : j.succ.castSucc = j.castSucc.succ := rfl
      rw [Hidx,HnodeLeft]
    have hLeftEnd : v j ∈ (chartAt (ComplexVector n) (c j.castSucc)).source := by
      have Hs := hsrc₁ j.castSucc
      rwa [HnodeLeft] at Hs
    have hRightStart : v j ∈ (chartAt (ComplexVector n) (c j.succ)).source := by
      have Hs := hsrc₀ j.succ
      rwa [HnodeRight] at Hs
    have hPairLeft : (chartPt (c j.castSucc) (fieldPolygonPoint q y v j.castSucc.castSucc),
        chartPt (c j.castSucc) (v j)) ∈ (e j.castSucc).target := by
      have Hp := hpair j.castSucc
      rwa [HnodeLeft] at Hp
    have hPairRight : (chartPt (c j.succ) (v j),
        chartPt (c j.succ) (fieldPolygonPoint q y v j.succ.succ)) ∈ (e j.succ).target := by
      have Hp := hpair j.succ
      rwa [HnodeRight] at Hp
    have HγLeft : γ j.castSucc = fieldNormalBranchCurve (c j.castSucc) (X j.castSucc) (e j.castSucc)
        (fieldPolygonPoint q y v j.castSucc.castSucc) (v j) := by
      dsimp only [γ]
      rw [HnodeLeft]
    have HγRight : γ j.succ = fieldNormalBranchCurve (c j.succ) (X j.succ) (e j.succ)
        (v j) (fieldPolygonPoint q y v j.succ.succ) := by
      dsimp only [γ]
      rw [HnodeRight]
    rw [HγLeft,HγRight]
    exact fieldPolygon_no_corner_at_normal_branches h hh O q y v hmin j (c j.castSucc) (c j.succ)
      (B j.castSucc) (B j.succ) (ρ j.castSucc) (ε j.castSucc) (ρ j.succ) (ε j.succ)
      (X j.castSucc) (X j.succ) (e j.castSucc) (e j.succ) (H j.castSucc) (H j.succ)
      (hsrc₀ j.castSucc) hLeftEnd hRightStart (hsrc₁ j.succ) hPairLeft hPairRight

end Yau.LeafProofs.L23Aux
