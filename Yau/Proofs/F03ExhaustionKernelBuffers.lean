import Yau.Proofs.F03MinimalKernelCandidate

/-! Genuine fixed compact chart buffers and domain-uniform C⁰ kernel bounds. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

theorem smoothExhaustion_eventually_contains_chart_compacts
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) (a b : M.Carrier)
    (K Q : Set (ComplexVector n)) (hK : IsCompact K) (hQ : IsCompact Q)
    (hKt : K ⊆ chartTarget a) (hQt : Q ⊆ chartTarget b) :
    ∃ J, ∀ j, J ≤ j →
      (∀ z ∈ K, chartInv a z ∈ O j) ∧ (∀ w ∈ Q, chartInv b w ∈ O j) := by
  have hKi : IsCompact (chartInv a '' K) := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono hKt)
  have hQi : IsCompact (chartInv b '' Q) := hQ.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) b).mono hQt)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (smoothExhaustion_eventually_contains_compact hO (hKi.union hQi))
  exact ⟨J,fun j hj => ⟨fun z hz => hJ j hj (Or.inl ⟨z,hz,rfl⟩),
    fun w hw => hJ j hj (Or.inr ⟨w,hw,rfl⟩)⟩⟩

theorem dirichletExhaustionKernels_compact_uniform_bound
    (g : SmoothMetric M) (hKahler : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) (a b : M.Carrier)
    (K Q : Set (ComplexVector n)) (hK : IsCompact K) (hQ : IsCompact Q)
    (hKt : K ⊆ chartTarget a) (hQt : Q ⊆ chartTarget b)
    (eps T : ℝ) (heps : 0 < eps) :
    ∃ B : ℝ, 0 < B ∧ ∀ j z, z ∈ K → ∀ w, w ∈ Q → ∀ t ∈ Icc eps T,
      |dirichletExhaustionKernels g hKahler μ hμ O hO j t (chartInv a z) (chartInv b w)| ≤ B := by
  let F : (ComplexVector n × ComplexVector n) × ℝ → ℝ := fun p =>
    dirichletKernelCandidate g hKahler μ hμ univ isOpen_univ p.2
      (chartInv a p.1.1) (chartInv b p.1.2)
  have hFc : ContinuousOn F ((K ×ˢ Q) ×ˢ Icc eps T) := by
    apply (dirichletKernelCandidate_smooth g hKahler μ hμ univ isOpen_univ a b).continuousOn.mono
    intro p hp
    exact ⟨⟨⟨hKt hp.1.1,mem_univ _⟩,⟨hQt hp.1.2,mem_univ _⟩⟩,heps.trans_le hp.2.1⟩
  obtain ⟨C,hC⟩ := ((hK.prod hQ).prod isCompact_Icc).bddAbove_image hFc
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro j z hz w hw t ht
  have hpos := heps.trans_le ht.1
  have hn : 0 ≤ dirichletExhaustionKernels g hKahler μ hμ O hO j t (chartInv a z) (chartInv b w) :=
    dirichletKernelCandidate_nonneg g hKahler μ hμ (O j) (hO.1 j).1 hpos _ _
  rw [abs_of_nonneg hn]
  exact (dirichletExhaustionKernels_le_univ g hKahler μ hμ O hO hpos _ _ j).trans
    ((hC ⟨((z,w),t),⟨⟨hz,hw⟩,ht⟩,rfl⟩).trans (le_max_right _ _))

end Yau.Proofs.F03Aux
