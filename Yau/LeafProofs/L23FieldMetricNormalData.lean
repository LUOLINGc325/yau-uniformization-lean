import Yau.LeafProofs.L23FieldMetricPairNeighborhood

/-! Proven actual normal endpoint data, packaged as an ordinary proposition. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

def FieldNormalEndpointData (h : HermitianField M) (c : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n)) : Prop :=
  IsOpen B ∧ chartPt c c ∈ B ∧ B ⊆ chartTarget c ∧ 0 < ρ ∧ 0 < ε ∧
  e.source = B ×ˢ Metric.ball (0 : ComplexVector n) ρ ∧
  Set.EqOn e (fun p => (p.1,X p 1)) e.source ∧
  ContDiffOn ℝ 3 (Function.uncurry X) (e.source ×ˢ Set.Ioo (-ε) (1+ε)) ∧
  ContDiffOn ℝ 3 e.symm e.target ∧
  (∀ p ∈ e.source, X p 0 = p.1 ∧ deriv (X p) 0 = p.2 ∧
    (∀ u ∈ Set.Ioo (-ε) (1+ε), X p u ∈ chartTarget c) ∧
    FieldGeodesicOn h (fun u => chartInv c (X p u)) (Set.Ioo (-ε) (1+ε)) ∧
    Set.MapsTo (fun u => chartInv c (X p u)) (Set.Icc (0 : ℝ) 1) O ∧
    inducedDistance h (chartInv c p.1) (chartInv c (X p 1))^2 = realMetricInChart h c p.1 p.2 p.2) ∧
  (∀ z ∈ B, (∀ u ∈ Set.Ioo (-ε) (1+ε), X (z,0) u = z) ∧
    HasFDerivAt (fun v => X (z,v) 1) (ContinuousLinearMap.id ℝ (ComplexVector n)) 0)

theorem exists_fieldNormalEndpointData (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) (O : Set M.Carrier) (hO : IsOpen O) (hc : c ∈ O) :
    ∃ (B : Set (ComplexVector n)) (ρ ε : ℝ)
      (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
      (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n)),
      FieldNormalEndpointData h c O B ρ ε X e :=
  localNormalEndpoint n M h hh c O hO hc

theorem fieldNormalEndpointData_diagonal_target
    (h : HermitianField M) (c : M.Carrier) (O : Set M.Carrier)
    (B : Set (ComplexVector n)) (ρ ε : ℝ)
    (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (H : FieldNormalEndpointData h c O B ρ ε X e) :
    (chartPt c c,chartPt c c) ∈ e.target := by
  rcases H with ⟨hB,hcB,hBsub,hρ,hε,hsource,heq,hX,hinv,hdata,hzero⟩
  have hp : (chartPt c c,(0 : ComplexVector n)) ∈ e.source := by
    rw [hsource]
    exact ⟨hcB,Metric.mem_ball_self hρ⟩
  have h₁ : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hezero : e (chartPt c c,0) = (chartPt c c,chartPt c c) := by
    have HE : e (chartPt c c,0) = (chartPt c c,X (chartPt c c,0) 1) := heq hp
    rw [(hzero _ hcB).1 1 h₁] at HE
    exact HE
  rw [← hezero]
  exact e.map_source hp

end Yau.LeafProofs.L23Aux
