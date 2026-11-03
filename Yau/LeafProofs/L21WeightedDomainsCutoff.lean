import Yau.LeafProofs.L21WeightedDomainsCore

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

/-- Each genuine boundary cutoff yields an actual compactly supported
joint weighted graph approximation. No boundary bound on zeroth order
coefficients and no graph-density premise is used. -/
theorem weightedDomains_cutoff_graph_approx {α β ι : Type*} [Fintype α] [Fintype ι]
    (K : ℝ) (hK : 0 ≤ K)
    (v : ι → X n) (a : β → α → ι → X n → ℂ) (b : β → α → X n → ℂ)
    (ha : ∀ r c i, ContDiffOn ℝ ∞ (a r c i) (Metric.ball 0 1))
    (hb : ∀ r c, ContDiffOn ℝ ∞ (b r c) (Metric.ball 0 1))
    (u : X n → α → ℂ) (w : X n → β → ℂ)
    (hu : ∀ c, MemLp (fun x => u x c) 2 (weightedBallMeasure n K))
    (hw : ∀ r, MemLp (fun x => w x r) 2 (weightedBallMeasure n K))
    (hRow : ∀ r (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball 0 1 →
      (∫ x, (ψ x : ℂ)*w x r ∂Yau.lebesgueC n) =
        ∫ x, ∑ c, u x c*Yau.LeafProofs.L14Aux.complexFormalAdjointTestRow v a b r c ψ x ∂Yau.lebesgueC n)
    (m : ℕ) :
    ∃ (L : Set (X n)) (U : ℕ → X n → α → ℂ), IsCompact L ∧ L ⊆ Metric.ball 0 1 ∧
      (∀ j c, ContDiff ℝ ∞ (fun x => U j x c) ∧ tsupport (fun x => U j x c) ⊆ L) ∧
      (∀ c, (∀ j, MemLp (fun x => U j x c-(boundaryCutoff m x : ℂ)*u x c)
          2 (weightedBallMeasure n K)) ∧
        Tendsto (fun j => ∫ x, ‖U j x c-(boundaryCutoff m x : ℂ)*u x c‖^2
          ∂weightedBallMeasure n K) atTop (𝓝 0)) ∧
      ∀ r, (∀ j, MemLp (fun x => Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (U j) x r-
          Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w x r)
          2 (weightedBallMeasure n K)) ∧
        Tendsto (fun j => ∫ x,
          ‖Yau.LeafProofs.L14Aux.complexFirstOrderSystemApply v a b (U j) x r-
            Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w x r‖^2
              ∂weightedBallMeasure n K) atTop (𝓝 0) := by
  have huLocal (c : α) := locallyL2On_of_weightedBall_memLp K (hu c)
  have hwLocal (r : β) := locallyL2On_of_weightedBall_memLp K (hw r)
  have hχ := contDiff_boundaryCutoff (E := X n) m
  have hcχ := hasCompactSupport_boundaryCutoff (E := X n) m
  have hsχ := tsupport_boundaryCutoff_subset_ball (E := X n) m
  apply weightedDomains_fixed_support_graph_approx K hK hcχ hsχ v a b ha hb
    (fun x c => (boundaryCutoff m x : ℂ)*u x c)
    (Yau.LeafProofs.L14Aux.localizedComplexSystemOutput v a (boundaryCutoff m) u w)
  · intro c
    exact Yau.LeafProofs.L14Aux.localizedComplexSystemInput_memLp _ hχ hcχ hsχ _ (huLocal c)
  · intro r
    exact Yau.LeafProofs.L14Aux.localizedComplexSystemOutput_memLp Metric.isOpen_ball v a ha _
      hχ hcχ hsχ u w huLocal hwLocal r
  · intro c
    exact tsupport_mul_subset_left.trans (tsupport_comp_subset Complex.ofReal_zero _)
  · intro r
    exact Yau.LeafProofs.L14Aux.localizedComplexSystemOutput_tsupport_subset v a _ u w r
  · exact Yau.LeafProofs.L14Aux.complex_firstOrder_rows_localize Metric.isOpen_ball v a b ha hb u w
      (fun c => locallyIntegrableOn_of_locallyL2On Metric.isOpen_ball (huLocal c))
      (fun r => locallyIntegrableOn_of_locallyL2On Metric.isOpen_ball (hwLocal r)) hRow
      _ hχ hcχ hsχ

end Yau.LeafProofs.L21Aux
