import Yau.Proofs.V03Elementary

/-! Order and convergence arguments for the actual EReal infima. These lemmas
also apply at infinite endpoints and do not require a nonnegative penalty. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

theorem ereal_iInf_eq_of_approximation {ι : Type*}
    (A B : ι → Prop) (cost : ι → ℝ)
    (happrox : ∀ i, A i → ∀ δ : ℝ, 0 < δ →
      ∃ k, A k ∧ B k ∧ |cost k - cost i| < δ) :
    (⨅ (i : ι) (_ : A i) (_ : B i), (cost i : EReal)) =
      ⨅ (i : ι) (_ : A i), (cost i : EReal) := by
  apply le_antisymm
  · refine le_iInf fun i => le_iInf fun hi => ?_
    by_contra hle
    obtain ⟨z, hz, hz'⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hle)
    have hz0 : 0 < z - cost i := by
      have := EReal.coe_lt_coe_iff.mp hz
      linarith
    obtain ⟨k, hk, hBk, hcost⟩ := happrox i hi (z - cost i) hz0
    have hkz : cost k < z := by
      have := (abs_lt.mp hcost).2
      linarith
    have hki : (⨅ (i : ι) (_ : A i) (_ : B i), (cost i : EReal)) ≤ cost k :=
      iInf_le_of_le k (iInf_le_of_le hk (iInf_le _ hBk))
    exact (not_lt_of_ge hki) ((EReal.coe_lt_coe_iff.mpr hkz).trans hz')
  · refine le_iInf fun i => le_iInf fun hi => le_iInf fun _ => ?_
    exact iInf₂_le i hi

theorem ereal_tendsto_of_sub_tendsto_zero {α : Type*} {l : Filter α}
    {f g : α → ℝ} {a : EReal}
    (hf : Tendsto (fun x => (f x : EReal)) l (𝓝 a))
    (hsub : Tendsto (fun x => g x - f x) l (𝓝 (0 : ℝ))) :
    Tendsto (fun x => (g x : EReal)) l (𝓝 a) := by
  have hz : Tendsto (fun x => ((g x - f x : ℝ) : EReal)) l (𝓝 (0 : EReal)) := by
    simpa only [EReal.coe_zero] using EReal.tendsto_coe.mpr hsub
  have hc : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, 0) :=
    EReal.continuousAt_add (Or.inr (by simp)) (Or.inr (by simp))
  have ht := hc.tendsto.comp (hf.prodMk_nhds hz)
  simpa only [Function.comp_def, ← EReal.coe_add, add_sub_cancel, add_zero] using ht

theorem ereal_tendsto_of_abs_sub_le_inv {f g : ℕ → ℝ} {a : EReal}
    (hf : Tendsto (fun ν => (f ν : EReal)) atTop (𝓝 a))
    (he : ∀ ν, |g ν - f ν| ≤ (ν + 1 : ℝ)⁻¹) :
    Tendsto (fun ν => (g ν : EReal)) atTop (𝓝 a) := by
  apply ereal_tendsto_of_sub_tendsto_zero hf
  apply squeeze_zero_norm
  · intro ν
    simpa only [Real.norm_eq_abs] using he ν
  · simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun ν : ℕ => 1 / ((ν : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))

end Yau.Blueprint.V03Proof
