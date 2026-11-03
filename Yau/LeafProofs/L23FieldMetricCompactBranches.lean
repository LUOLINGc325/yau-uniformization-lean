import Yau.LeafProofs.L23FieldMetricNormalData
import Yau.LeafProofs.L23LocalDistanceSupportShortEdges

/-! Genuine short normal branches cover exact minimizing polygons in a compact buffer. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
variable {n N : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

def HasFieldNormalBranch (h : HermitianField M) (O : Set M.Carrier) (q y : M.Carrier) : Prop :=
  ∃ (c : M.Carrier) (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n)),
    FieldNormalEndpointData h c O B ρ ε X e ∧
      q ∈ (chartAt (ComplexVector n) c).source ∧ y ∈ (chartAt (ComplexVector n) c).source ∧
      (chartPt c q,chartPt c y) ∈ e.target

theorem exists_uniform_fieldNormalBranch
    (h : HermitianField M) (hh : MetricSmooth h) (O S : Set M.Carrier)
    (hO : IsOpen O) (hS : IsCompact S) (hSO : S ⊆ O) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ S, ∀ y : M.Carrier,
      inducedDistance h q y < δ → HasFieldNormalBranch h O q y := by
  letI := metricSpaceOfField h hh
  apply uniform_pairs_of_compact S hS (HasFieldNormalBranch h O)
  intro c hc
  obtain ⟨B,ρ,ε,X,e,H⟩ := exists_fieldNormalEndpointData h hh c O hO (hSO hc)
  obtain ⟨U,hU,hcU,hUO,hUchart,hpairs⟩ := exists_open_chart_pair_neighborhood h hh c O hO (hSO hc) e
    (fieldNormalEndpointData_diagonal_target h c O B ρ ε X e H)
  refine ⟨U,hU,hcU,?_⟩
  intro q hq y hy
  exact ⟨c,B,ρ,ε,X,e,H,hUchart hq,hUchart hy,hpairs q hq y hy⟩

theorem fieldPolygonPoint_mem (S : Set M.Carrier) (q y : M.Carrier) (v : Fin N → M.Carrier)
    (hq : q ∈ S) (hy : y ∈ S) (hv : ∀ i, v i ∈ S) (i : Fin (N+2)) :
    fieldPolygonPoint q y v i ∈ S := by
  refine Fin.cases hq (fun j => ?_) i
  change Fin.lastCases y v j ∈ S
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simpa only [Fin.lastCases_last] using hy
  · simpa only [Fin.lastCases_castSucc] using hv k

theorem exists_compact_normal_polygon
    (h : HermitianField M) (hh : MetricSmooth h) (O S : Set M.Carrier)
    (hO : IsOpen O) (hS : IsCompact S) (hSO : S ⊆ O) (q y : M.Carrier)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ γ : IntegrableCurve h q y,
      curveLength h γ.1 < inducedDistance h q y+ε ∧ Set.MapsTo γ.1 (Set.Icc (0 : ℝ) 1) S) :
    ∃ (N : ℕ) (v : Fin N → M.Carrier), (∀ i, v i ∈ S) ∧
      fieldPolygonEnergy h q y v = inducedDistance h q y^2 ∧
      (∀ w : Fin N → M.Carrier, fieldPolygonEnergy h q y v ≤ fieldPolygonEnergy h q y w) ∧
      ∀ i : Fin (N+1), HasFieldNormalBranch h O
        (fieldPolygonPoint q y v i.castSucc) (fieldPolygonPoint q y v i.succ) := by
  obtain ⟨δ,hδ,hbranches⟩ := exists_uniform_fieldNormalBranch h hh O S hO hS hSO
  obtain ⟨N,v,hv,heq,hmin,hshort⟩ := exists_fieldPolygon_exact_with_short_edges h hh S hS q y hnear δ hδ
  obtain ⟨γ,_,hγ⟩ := hnear 1 zero_lt_one
  have hq : q ∈ S := by
    have H := hγ (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    rwa [γ.1.start_eq] at H
  have hy : y ∈ S := by
    have H := hγ (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    rwa [γ.1.finish_eq] at H
  exact ⟨N,v,hv,heq,hmin,(fun i => hbranches _ (fieldPolygonPoint_mem S q y v hq hy hv i.castSucc)
    _ (hshort i))⟩

end Yau.LeafProofs.L23Aux
