import Yau.LeafProofs.L23FieldMetricExponentialSecondJet
import Yau.LeafProofs.L23FieldMetricEndpointInverse
import Yau.LeafProofs.L23FieldMetricVariationNeighborhood

/-! The genuine static parallel-endpoint variation, with all actual first and second jets. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
set_option maxHeartbeats 1200000

theorem parallelEndpointVariation (n : ℕ) : ParallelEndpointVariationGap n := by
  intro M h hh O hO γ ε hε hγ hγO
  letI := manifold_realSmooth M
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-ε) (1+ε) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  obtain ⟨δP,hδP,P,hP1,hPsub,HP,hpair⟩ := exists_endpoint_parallel_frame h hh γ _ isOpen_Ioo hunit hγ.1
  let Q := fun u => (P u).toContinuousLinearMap
  obtain ⟨δA,r,hδA,hr,hA,hAO⟩ := exists_parallelExpVariation_neighborhood h hh γ Q _ isOpen_Ioo
    (by intro t ht; constructor <;> linarith [ht.1,ht.2]) HP O hO (hγ.1.mono hPsub) hγO
  obtain ⟨e₀,he₀,he₀0,he₀exp,he₀inv⟩ := exists_preferred_exp_endpoint h hh (γ 1)
  let e := e₀.restrOpen (Metric.ball (0 : ComplexVector n) r) Metric.isOpen_ball
  let δ := min δA (min δP (ε/2))
  have hδ : 0 < δ := lt_min hδA (lt_min hδP (by positivity))
  have hδε : δ < ε := lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (half_lt_self hε)
  have hsubA : Set.Ioo (-δ) (1+δ) ⊆ Set.Ioo (-δA) (1+δA) := by
    intro u hu
    constructor <;> linarith [hu.1,hu.2,min_le_left δA (min δP (ε/2))]
  have hsubP : Set.Ioo (-δ) (1+δ) ⊆ Set.Ioo (-δP) (1+δP) := by
    intro u hu
    have H : δ ≤ δP := le_trans (min_le_right _ _) (min_le_left _ _)
    constructor <;> linarith [hu.1,hu.2]
  let A := parallelExpVariation h γ Q
  refine ⟨δ,e,P,A,hδ,hδε,⟨he₀,Metric.mem_ball_self hr⟩,he₀0,?_,?_,?_,?_,hP1,?_,?_⟩
  · exact hA.mono (fun p hp => ⟨hsubA hp.1,hp.2.2⟩)
  · exact he₀inv.mono (fun x hx => hx.1)
  · intro u hu
    exact parallelExpVariation_zero h hh γ Q u
  · intro v hv
    refine ⟨parallelExpVariation_initial h hh γ Q v,?_,?_⟩
    · change fieldExp h (γ 1) ((1 : ℝ) • Q 1 v) = e₀ v
      rw [one_smul]
      dsimp only [Q]
      rw [hP1]
      exact (he₀exp hv.1).symm
    · intro u hu
      have Htime : u ∈ Set.Ioo (-δA) (1+δA) := by constructor <;> linarith [hu.1,hu.2]
      have Hpoint : (u,v) ∈ Set.Ioo (-δA) (1+δA) ×ˢ Metric.ball (0 : ComplexVector n) r := ⟨Htime,hv.2⟩
      exact hAO Hpoint
  · intro u hu
    exact hpair u (hsubP hu)
  · intro c u hu hc
    have hc' : γ u ∈ (chartAt (ComplexVector n) c).source := by simpa only [extChartAt_source] using hc
    refine ⟨?_,parallelExpVariation_chart_firstJet h hh γ Q c u hc',?_⟩
    · intro w
      have H := (HP c u (hsubP hu) hc').clm_apply (hasDerivAt_const u w)
      convert! H using 1 <;>
        simp only [chartParallelCoefficient,geoChartState,Q,ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.neg_apply,map_zero,zero_add,add_zero]
      all_goals rfl
    · intro w
      exact parallelExpVariation_chart_radial_secondJet h hh γ Q c u hc' w

end Yau.LeafProofs.L23Aux
