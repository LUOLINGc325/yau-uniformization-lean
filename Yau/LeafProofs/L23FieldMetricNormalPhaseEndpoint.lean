import Yau.LeafProofs.L23FieldMetricNormalEndpoint

/-! The normal endpoint chart retaining its genuine position-velocity flow. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem exists_C3_normal_phase_endpoint
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (O : Set M.Carrier) (hO : IsOpen O) (hc : c ∈ O) :
    ∃ (B : Set (ComplexVector n)) (ρ ε : ℝ)
      (η : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
      (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n)),
      IsOpen B ∧ chartPt c c ∈ B ∧ B ⊆ chartTarget c ∧ 0 < ρ ∧ 0 < ε ∧
      e.source = B ×ˢ Metric.ball (0 : ComplexVector n) ρ ∧
      Set.EqOn e (fun p => (p.1,(η p 1).1)) e.source ∧
      ContDiffOn ℝ 3 (Function.uncurry η) (e.source ×ˢ Set.Ioo (-ε) (1+ε)) ∧
      ContDiffOn ℝ 3 e.symm e.target ∧
      (∀ p ∈ e.source, η p 0 = p ∧
        (∀ u ∈ Set.Ioo (-ε) (1+ε), (η p u).1 ∈ chartTarget c ∧
          HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u) ∧
        FieldGeodesicOn h (fun u => chartInv c (η p u).1) (Set.Ioo (-ε) (1+ε)) ∧
        Set.MapsTo (fun u => chartInv c (η p u).1) (Set.Icc (0 : ℝ) 1) O) ∧
      (∀ z ∈ B,
        (∀ u ∈ Set.Ioo (-ε) (1+ε), η (z,0) u = (z,0)) ∧
        HasFDerivAt (fun v => (η (z,v) 1).1) (ContinuousLinearMap.id ℝ (ComplexVector n)) 0) := by
  obtain ⟨B₀,ρ₀,ε,η,hB₀,hcB₀,hB₀sub,hρ₀,hε,hη,hηdata,hηzero⟩ :=
    exists_C3_unit_chart_geodesic_family h hh c O hO hc
  let g : ComplexVector n × ComplexVector n → ComplexVector n := fun p => (η p 1).1
  have h₁ : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hg : ContDiffOn ℝ 3 g (B₀ ×ˢ Metric.ball (0 : ComplexVector n) ρ₀) :=
    (hη.comp (contDiffOn_id.prodMk contDiffOn_const) (fun p hp => ⟨hp,h₁⟩)).fst
  have hgzero : ∀ z ∈ B₀, g (z,0) = z := by
    intro z hz
    exact congrArg Prod.fst ((hηzero z hz).1 1 h₁)
  obtain ⟨B,ρ,e,hB,hcB,hBB₀,hρ,hesource,hesub,heq,heinv⟩ :=
    exists_product_endpoint_chart B₀ hB₀ (chartPt c c) hcB₀ ρ₀ hρ₀ g hg hgzero
      (hηzero (chartPt c c) hcB₀).2
  exact ⟨B,ρ,ε,η,e,hB,hcB,(fun z hz => hB₀sub (hBB₀ hz)),hρ,hε,hesource,heq,
    hη.mono (fun p hp => ⟨hesub hp.1,hp.2⟩),heinv,
    (fun p hp => hηdata p (hesub hp)),(fun z hz => hηzero z (hBB₀ hz))⟩

end Yau.LeafProofs.L23Aux
