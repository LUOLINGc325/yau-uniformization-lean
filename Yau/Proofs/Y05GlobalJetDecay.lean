import Yau.Proofs.Y05TransitionJets

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint Filter
open scoped Topology ContDiff

variable {n : ℕ}

/-- A finite initial part of an analytic transition family is absorbed in
one enlarged decay constant using its actual germ cocycle. -/
theorem global_transition_jet_decay
    {T : ℕ → ℕ → ComplexVector n → ComplexVector n} {s : ℕ → ℝ} {σ : ℝ} {d : ℕ}
    (hs : ∀ k, 0 < s k) (hsm : Monotone s) (hσ : 0 < σ)
    (hTa : ∀ k l, k ≤ l → AnalyticAt ℂ (T k l) 0)
    (hT0 : ∀ k l, k ≤ l → T k l 0 = 0)
    (hcocycle : ∀ k j l, k ≤ j → j ≤ l →
      (T j l ∘ T k j) =ᶠ[𝓝 0] T k l)
    {U : ℝ} (hU : 1 ≤ U) (huniform : ∀ k l, k ≤ l → jetNorm (T k l) d ≤ U)
    {J : ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hlate : ∀ k l, J ≤ k → k ≤ l →
      jetNorm (T k l) d ≤ D * min 1 (Real.exp (D * s k - σ * s l))) :
    ∃ K : ℝ, 0 < K ∧ ∀ k l, k ≤ l →
      jetNorm (T k l) d ≤ K * min 1 (Real.exp (K * s k - σ * s l)) := by
  let A := compositionJetConstant d * D * U ^ d
  let R := (D + σ) * s J / s 0
  let K := 1 + U + A + D + R
  have hU0 : 0 ≤ U := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hA : 0 ≤ A := by
    dsimp [A, compositionJetConstant]
    positivity
  have hR : 0 ≤ R := div_nonneg
    (mul_nonneg (add_nonneg hD0 hσ.le) (hs J).le) (hs 0).le
  have hK : 0 < K := by dsimp [K]; linarith
  have hUK : U ≤ K := by dsimp [K]; linarith
  have hAK : A ≤ K := by dsimp [K]; linarith
  have hDK : D ≤ K := by dsimp [K]; linarith
  have hRK : R ≤ K := by dsimp [K]; linarith
  have hR0 : R * s 0 = (D + σ) * s J := by
    dsimp [R]
    field_simp [(hs 0).ne']
  have hK0 : (D + σ) * s J ≤ K * s 0 := by
    rw [← hR0]
    exact mul_le_mul_of_nonneg_right hRK (hs 0).le
  have hKsD (k : ℕ) : D * s J ≤ K * s k := by
    have H := mul_le_mul_of_nonneg_left (hsm (Nat.zero_le k)) hK.le
    nlinarith [mul_nonneg hσ.le (hs J).le]
  have hKsσ (k : ℕ) : σ * s J ≤ K * s k := by
    have H := mul_le_mul_of_nonneg_left (hsm (Nat.zero_le k)) hK.le
    nlinarith [mul_nonneg hD0 (hs J).le]
  refine ⟨K, hK, ?_⟩
  intro k l hkl
  by_cases hk : J ≤ k
  · apply (hlate k l hk hkl).trans
    have hδ : min 1 (Real.exp (D * s k - σ * s l)) ≤
        min 1 (Real.exp (K * s k - σ * s l)) := by
      apply min_le_min le_rfl
      apply Real.exp_le_exp.mpr
      nlinarith [hs k]
    exact mul_le_mul hDK hδ
      (le_min (by norm_num) (Real.exp_pos _).le) hK.le
  by_cases hl : l ≤ J
  · have hdiff : 0 ≤ K * s k - σ * s l := by
      have H := mul_le_mul_of_nonneg_left (hsm hl) hσ.le
      linarith [hKsσ k]
    rw [min_eq_left (Real.one_le_exp_iff.mpr hdiff), mul_one]
    exact (huniform k l hkl).trans hUK
  · have hkJ : k ≤ J := by omega
    have hJl : J ≤ l := by omega
    let δ := min 1 (Real.exp (D * s J - σ * s l))
    have hδ : 0 ≤ δ := le_min (by norm_num) (Real.exp_pos _).le
    have hgb (m : ℕ) (hm : m ≤ d) : ‖iteratedFDeriv ℂ m (T J l) 0‖ ≤ D * δ :=
      (norm_jet_component_le (T J l) hm).trans (hlate J l le_rfl hJl)
    have hfb (m : ℕ) (_hm : 1 ≤ m) (hm : m ≤ d) :
        ‖iteratedFDeriv ℂ m (T k J) 0‖ ≤ U :=
      (norm_jet_component_le (T k J) hm).trans (huniform k J hkJ)
    have H := finiteJetNorm_comp_uniform_le
      (hTa k J hkJ).contDiffAt (hTa J l hJl).contDiffAt (hT0 k J hkJ)
      hU (mul_nonneg hD0 hδ) hgb hfb
    have heq := finiteJetNorm_congr (hcocycle k J l hkJ hJl) d
    have hbound : jetNorm (T k l) d ≤ A * δ := by
      change finiteJetNorm (T k l) d ≤ A * δ
      rw [← heq]
      exact H.trans_eq (by dsimp [A]; ring)
    apply hbound.trans
    have hδK : δ ≤ min 1 (Real.exp (K * s k - σ * s l)) :=
      min_le_min le_rfl (Real.exp_le_exp.mpr (by linarith [hKsD k]))
    exact mul_le_mul hAK hδK hδ hK.le

theorem shrinking_grid_global_jet_decay {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {ρ : STF X} {r₀ r₁ σ C Cb t₀ : ℝ}
    {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hc : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    {tk : ℕ → ℝ} (htk : StrictMono tk) (hlate : ∀ k, t₀ ≤ tk k)
    (hs : ∀ k, 0 < ρ o (tk k)) (hsm : Monotone (fun k => ρ o (tk k)))
    (hdiv : Tendsto (fun k => ρ o (tk k)) atTop atTop) (d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ k l, k ≤ l → jetNorm (F (tk k) (tk l)) d ≤
      K * min 1 (Real.exp (K * ρ o (tk k) - σ * ρ o (tk l))) := by
  have htdiv := shrinking_clock_time_tendsto hc htk hlate hdiv
  obtain ⟨U, hU, huniform⟩ := shrinking_uniform_transition_jets hc d
  rcases hc with ⟨hr, hr0, hσ, hC, hcharts, htrans, hcomp, hf0, hinv, hdec, hj, hreg⟩
  obtain ⟨Cd, Td, hdecay⟩ := hj d
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (htdiv.eventually (eventually_ge_atTop Td))
  let D := max 1 Cd
  have hD : 1 ≤ D := le_max_left _ _
  have hCd : Cd ≤ D := le_max_right _ _
  apply global_transition_jet_decay hs hsm hσ
    (fun k l hkl => Yau.NodeProofs.U02Proof.holomorphic_analyticOnNhd Metric.isOpen_ball
      (htrans (tk k) (tk l) (hlate k) (htk.monotone hkl)).1 0 (Metric.mem_ball_self hr))
    (fun k l hkl => (htrans (tk k) (tk l) (hlate k) (htk.monotone hkl)).2.2.1)
    (fun k j l hkj hjl => hcomp (tk k) (tk j) (tk l) (hlate k)
      (htk.monotone hkj) (htk.monotone hjl))
    hU (fun k l hkl => huniform (tk k) (tk l) (hlate k) (htk.monotone hkl))
    (J := J) hD
  intro k l hk hkl
  apply (hdecay (tk k) (tk l) (hJ k hk) (htk.monotone hkl)).trans
  have hδ : min 1 (Real.exp (Cd * ρ o (tk k) - σ * ρ o (tk l))) ≤
      min 1 (Real.exp (D * ρ o (tk k) - σ * ρ o (tk l))) := by
    apply min_le_min le_rfl
    apply Real.exp_le_exp.mpr
    nlinarith [hs k]
  exact mul_le_mul hCd hδ (le_min (by norm_num) (Real.exp_pos _).le)
    (le_trans zero_le_one hD)

end Yau.Proofs.Y05Aux
