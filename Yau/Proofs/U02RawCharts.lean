import Yau.Proofs.U02Clock

/-! Compact raw-chart data and the actual orbit identity along the
physical times of the original polynomial models. -/

open scoped Manifold Topology ContDiff
open Filter Metric

noncomputable section
namespace Yau.NodeProofs.U02Proof

open Yau Blueprint

theorem raw_compact_data {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {K : Set (Pt X)} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∃ V : Set (Pt X), IsOpen V ∧ K ⊆ V ∧
      MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) (f (tk k)) V ∧
      (∀ x ∈ V, f (tk k) x ∈ ball 0 r0 ∧ Phi (tk k) (f (tk k) x) = x ∧
        ∀ t', tk k ≤ t' → f (tk k) x ∈ ball 0 r1 →
          f t' x = F (tk k) t' (f (tk k) x)) ∧
      (∀ x ∈ K, ‖f (tk k) x‖ ≤ Real.exp (-sigma * rho o (tk k))) := by
  rcases hc with ⟨_, _, _, _, _, _, _, _, hinverse, hdecay, _, _⟩
  obtain ⟨T1, _hT1, h1⟩ := hinverse K hK
  obtain ⟨T2, h2⟩ := hdecay K hK
  filter_upwards [eventually_models_time_ge hf hp ht (max T1 T2)] with k hk
  obtain ⟨V, hV, hKV, hdf, hv⟩ := h1 (tk k) ((le_max_left _ _).trans hk)
  exact ⟨V, hV, hKV, hdf, hv, h2 (tk k) ((le_max_right _ _).trans hk)⟩

theorem raw_compact_orbit {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) {K : Set (Pt X)} (hK : IsCompact K) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      f (tk (k + 1)) x = F (tk k) (tk (k + 1)) (f (tk k) x) := by
  have hr1 : 0 < r1 := hc.1
  have hsigma : 0 < sigma := hc.2.2.1
  have hexp : Tendsto (fun k => Real.exp (-sigma * rho o (tk k))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hp.2.1.const_mul_atTop hsigma)
  have hsmall : ∀ᶠ k in atTop, Real.exp (-sigma * rho o (tk k)) < r1 :=
    hexp.eventually (gt_mem_nhds hr1)
  filter_upwards [raw_compact_data hf hc hp ht hK, hsmall] with k hk hsk
  obtain ⟨V, _hV, hKV, _hdf, hv, hb⟩ := hk
  intro x hx
  apply (hv x (hKV hx)).2.2 (tk (k + 1)) (hp.1.monotone (Nat.le_succ k))
  simpa only [mem_ball, dist_zero_right] using (hb x hx).trans_lt hsk

theorem raw_basepoint_zero {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P rho : STF X} {r0 r1 sigma C Cb t0 : ℝ}
    {Phi : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P rho)
    (hc : ShrinkingCharts X o h rho r0 r1 sigma C Cb t0 Phi F f)
    (hp : PolynomialModels X o rho F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) : ∀ᶠ k in atTop, f (tk k) o = 0 := by
  rcases hc with ⟨_, _, _, _, _, _, _, hz, _⟩
  filter_upwards [eventually_models_time_ge hf hp ht t0] with k hk
  exact hz (tk k) hk

end Yau.NodeProofs.U02Proof
