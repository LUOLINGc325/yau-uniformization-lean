import Yau.LeafProofs.L23FieldMetricEndpointChart

/-! The actual C3 normal endpoint chart before the Gauss distance identity. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem exists_C3_normal_endpoint
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (O : Set M.Carrier) (hO : IsOpen O) (hc : c ∈ O) :
    ∃ (B : Set (ComplexVector n)) (ρ ε : ℝ)
      (X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n)
      (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n)),
      IsOpen B ∧ chartPt c c ∈ B ∧ B ⊆ chartTarget c ∧ 0 < ρ ∧ 0 < ε ∧
      e.source = B ×ˢ Metric.ball (0 : ComplexVector n) ρ ∧
      Set.EqOn e (fun p => (p.1,X p 1)) e.source ∧
      ContDiffOn ℝ 3 (Function.uncurry X) (e.source ×ˢ Set.Ioo (-ε) (1+ε)) ∧
      ContDiffOn ℝ 3 e.symm e.target ∧
      (∀ p ∈ e.source, X p 0 = p.1 ∧ deriv (X p) 0 = p.2 ∧
        (∀ u ∈ Set.Ioo (-ε) (1+ε), X p u ∈ chartTarget c) ∧
        FieldGeodesicOn h (fun u => chartInv c (X p u)) (Set.Ioo (-ε) (1+ε)) ∧
        Set.MapsTo (fun u => chartInv c (X p u)) (Set.Icc (0 : ℝ) 1) O) ∧
      (∀ z ∈ B,
        (∀ u ∈ Set.Ioo (-ε) (1+ε), X (z,0) u = z) ∧
        HasFDerivAt (fun v => X (z,v) 1) (ContinuousLinearMap.id ℝ (ComplexVector n)) 0) := by
  obtain ⟨B₀,hρ₀,ε,η,hB₀,hcB₀,hB₀sub,hρ₀pos,hε,hη,hηdata,hηzero⟩ :=
    exists_C3_unit_chart_geodesic_family h hh c O hO hc
  let g : ComplexVector n × ComplexVector n → ComplexVector n := fun p => (η p 1).1
  have h₁ : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have h₀ : (0 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hg : ContDiffOn ℝ 3 g (B₀ ×ˢ Metric.ball (0 : ComplexVector n) hρ₀) :=
    (hη.comp (contDiffOn_id.prodMk contDiffOn_const) (fun p hp => ⟨hp,h₁⟩)).fst
  have hgzero : ∀ z ∈ B₀, g (z,0) = z := by
    intro z hz
    exact congrArg Prod.fst ((hηzero z hz).1 1 h₁)
  obtain ⟨B,ρ,e,hB,hcB,hBB₀,hρ,hesource,hesub,heq,heinv⟩ :=
    exists_product_endpoint_chart B₀ hB₀ (chartPt c c) hcB₀ hρ₀ hρ₀pos g hg hgzero
      (hηzero (chartPt c c) hcB₀).2
  let X : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n := fun p u => (η p u).1
  have hX : ContDiffOn ℝ 3 (Function.uncurry X) (e.source ×ˢ Set.Ioo (-ε) (1+ε)) :=
    hη.fst.mono (fun p hp => ⟨hesub hp.1,hp.2⟩)
  refine ⟨B,ρ,ε,X,e,hB,hcB,(fun z hz => hB₀sub (hBB₀ hz)),hρ,hε,hesource,heq,hX,heinv,?_,?_⟩
  · intro p hp
    have H := hηdata p (hesub hp)
    have Hd := (ContinuousLinearMap.fst ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt 0
      (H.2.1 0 h₀).2
    have Hd' : HasDerivAt (X p) p.2 0 := by
      convert! Hd using 1
      simp only [chartGeodesicSpray,H.1]
      rfl
    exact ⟨congrArg Prod.fst H.1,Hd'.deriv,(fun u hu => (H.2.1 u hu).1),H.2.2.1,H.2.2.2⟩
  · intro z hz
    exact ⟨fun u hu => congrArg Prod.fst ((hηzero z (hBB₀ hz)).1 u hu),
      (hηzero z (hBB₀ hz)).2⟩

end Yau.LeafProofs.L23Aux
