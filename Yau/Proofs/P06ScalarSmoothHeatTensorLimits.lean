import Yau.Proofs.P06ScalarSmoothHeatTensorJets

/-! Uniform convergence of the finite coordinate words upgrades to
the literal iterated Fréchet derivative norm used in the initial class. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.ScalarSmooth

theorem iteratedFDeriv_uniform_small_of_words {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (b : Basis ι ℝ E) (F : ℝ → E → ℝ)
    (hF : ∀ t, 0 < t → ContDiff ℝ ∞ (F t))
    (hw : ∀ w : List ι, ∀ ε : ℝ, 0 < ε → ∃ τ > 0,
      ∀ t, 0 < t → t < τ → ∀ z, |regularityCoefficientWord b w (F t) z| < ε)
    (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ z, ‖iteratedFDeriv ℝ j (F t) z‖ < ε := by
  obtain ⟨C,hC,hbound⟩ := iteratedFDeriv_norm_lt_of_words b j
  have hδ : 0 < ε / C := div_pos hε hC
  have hp (p : Fin j → ι) : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ z, |regularityCoefficientWord b (List.ofFn p) (F t) z| < ε / C := by
    obtain ⟨τ,hτ,hh⟩ := hw (List.ofFn p) (ε/C) hδ
    filter_upwards [Ioo_mem_nhdsGT hτ] with t ht
    exact hh t ht.1 ht.2
  have hall := eventually_all.mpr hp
  obtain ⟨τ,hτ,hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hall
  refine ⟨τ,hτ,?_⟩
  intro t ht htτ z
  have h := hbound (F t) (hF t ht) (ε/C) hδ z (fun p => hh ⟨ht,htτ⟩ p z)
  simpa only [mul_div_cancel₀ _ hC.ne'] using h

theorem iteratedFDeriv_comp_linear_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E →L[ℝ] F) (f : F → ℝ) (hf : ContDiff ℝ ∞ f) (j : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ j (f ∘ e) z‖ ≤
      ‖iteratedFDeriv ℝ j f (e z)‖ * ‖e‖^j := by
  rw [e.iteratedFDeriv_comp_right hf z (by simp)]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j f (e z)) (fun _ : Fin j => e)

end Yau.NodeProofs.P06Aux.ScalarSmooth
