import Yau.Proofs.C02ODELocalFlow

/-! Uniform local identification of two actual solution families. Joint
continuity supplies one common rectangle; uniqueness is then applied in time. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.C02Proof

variable {A E : Type*} [PseudoMetricSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eventuallyEq_ODE_families
    {F : E → E} {f g : A → ℝ → E} {a₀ : A} {N : Set (A × ℝ)}
    (hF : ContDiffAt ℝ 1 F (f a₀ 0))
    (hf : ContinuousAt (Function.uncurry f) (a₀, 0))
    (hg : ContinuousAt (Function.uncurry g) (a₀, 0))
    (hN : N ∈ 𝓝 (a₀, 0))
    (hinit : ∀ a, (a, 0) ∈ N → f a 0 = g a 0)
    (hfe : ∀ p ∈ N, HasDerivAt (f p.1) (F (f p.1 p.2)) p.2)
    (hge : ∀ p ∈ N, HasDerivAt (g p.1) (F (g p.1 p.2)) p.2) :
    Function.uncurry f =ᶠ[𝓝 (a₀, 0)] Function.uncurry g := by
  obtain ⟨L, W, hW, hLip⟩ := hF.exists_lipschitzOnWith
  have hzero : f a₀ 0 = g a₀ 0 := hinit a₀ (mem_of_mem_nhds hN)
  have hfg : {p : A × ℝ | f p.1 p.2 ∈ W ∧ g p.1 p.2 ∈ W} ∈ 𝓝 (a₀, 0) := by
    apply Filter.inter_mem (hf.preimage_mem_nhds hW)
    apply hg.preimage_mem_nhds
    simpa only [Function.uncurry_apply_pair, ← hzero] using hW
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hN hfg)
  have hrect : Metric.ball a₀ δ ×ˢ Ioo (-δ) δ ⊆
      {p : A × ℝ | p ∈ N ∧ f p.1 p.2 ∈ W ∧ g p.1 p.2 ∈ W} := by
    intro p hp
    have hball : p ∈ Metric.ball (a₀, 0) δ := by
      simpa only [← ball_prod_same, Real.ball_eq_Ioo, zero_sub, zero_add] using hp
    rcases hsub hball with ⟨hpN, hpf, hpg⟩
    exact ⟨hpN, hpf, hpg⟩
  have hrect_nhds : Metric.ball a₀ δ ×ˢ Ioo (-δ) δ ∈ 𝓝 (a₀, 0) :=
    (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds
      ⟨Metric.mem_ball_self hδ, by constructor <;> linarith⟩
  filter_upwards [hrect_nhds] with p hp
  have hzero_time : (0 : ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hline (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      (p.1, t) ∈ N ∧ f p.1 t ∈ W ∧ g p.1 t ∈ W :=
    hrect (show (p.1, t) ∈ Metric.ball a₀ δ ×ˢ Ioo (-δ) δ from ⟨hp.1, ht⟩)
  have hz : (p.1, (0 : ℝ)) ∈ N := (hline 0 hzero_time).1
  exact ODE_solution_unique_of_mem_Ioo
    (v := fun _ => F) (s := fun _ => W) (fun _ _ => hLip) hzero_time
    (fun t ht => ⟨hfe (p.1, t) (hline t ht).1, (hline t ht).2.1⟩)
    (fun t ht => ⟨hge (p.1, t) (hline t ht).1, (hline t ht).2.2⟩)
    (hinit p.1 hz) hp.2

end Yau.Blueprint.C02Proof
