import Yau.Proofs.C03MovingFamily

/-! One parameter neighborhood works for the entire compact trial path. -/

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem movingTrial_eventually_mapsTo (γ W : ℝ → E) (Q : E)
    (J S : Set ℝ) (hJ : IsOpen J) (hS : IsCompact S) (hSJ : S ⊆ J)
    (hγ : ContinuousOn γ J) (hW : ContinuousOn W J)
    (U : Set E) (hU : IsOpen U) (himage : MapsTo γ S U) :
    ∀ᶠ a : ℂ in 𝓝 0, ∀ t ∈ S, movingTrial γ W Q t a ∈ U := by
  apply hS.eventually_forall_of_forall_eventually
  intro t ht
  have hγt : ContinuousAt γ t := hγ.continuousAt (hJ.mem_nhds (hSJ ht))
  have hWt : ContinuousAt W t := hW.continuousAt (hJ.mem_nhds (hSJ ht))
  have hc : ContinuousAt (fun p : ℂ × ℝ => movingTrial γ W Q p.2 p.1) (0, t) := by
    unfold movingTrial
    exact ((hγt.comp continuousAt_snd).add
      (continuousAt_fst.smul (hWt.comp continuousAt_snd))).add
      ((((Complex.continuous_ofReal.continuousAt.comp continuousAt_snd).div_const 2).mul
        (continuousAt_fst.pow 2)).smul continuousAt_const)
  have hm : movingTrial γ W Q t 0 ∈ U := by
    rw [movingTrial_zero_parameter]
    exact himage ht
  exact hc.preimage_mem_nhds (hU.mem_nhds hm)

section RealSmooth
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem movingTrial_contDiffOn_order (γ W : ℝ → E) (Q : E) (J : Set ℝ)
    (k : ℕ∞ω) (hγ : ContDiffOn ℝ k γ J) (hW : ContDiffOn ℝ k W J) :
    ContDiffOn ℝ k (Function.uncurry (movingTrial γ W Q)) (J ×ˢ Set.univ) := by
  have hγ' : ContDiffOn ℝ k (fun p : ℝ × ℂ => γ p.1) (J ×ˢ Set.univ) :=
    hγ.comp contDiffOn_fst (fun _ hp => hp.1)
  have hW' : ContDiffOn ℝ k (fun p : ℝ × ℂ => W p.1) (J ×ˢ Set.univ) :=
    hW.comp contDiffOn_fst (fun _ hp => hp.1)
  have ht : ContDiffOn ℝ k (fun p : ℝ × ℂ => (p.1 : ℂ)) (J ×ˢ Set.univ) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_fst
  exact (hγ'.add (contDiffOn_snd.smul hW')).add
    (((ht.div_const 2).mul (contDiffOn_snd.pow 2)).smul_const Q)

end RealSmooth
end Yau.Proofs.C03Aux
