import Yau.Blueprint.ConcreteExtensions

/-! Source-scope/domain plumbing only. U02 and all analytic producers remain unproved. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
noncomputable section
namespace Yau.Blueprint.U02SourceScope
open Yau Yau.Blueprint

theorem same_clock_gate {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {ρ : STF X} {time : ℝ → ℝ} {s₀ : ℝ} {s : ℕ → ℝ}
    (hc : Alignment.ClockParameter X o h ρ time s₀)
    (hs : ∀ k, s₀ ≤ s k) : ∀ᶠ k in atTop, 0 ≤ time (s k) :=
  Filter.Eventually.of_forall (fun k => (hc.2.2.1 (s k) (hs k)).1.le)

/-- The actual nonnegative-time growth bound suffices even if its constant
is not positive. No bound or regularity at negative physical times is used. -/
theorem physical_time_cofinal {tk v : ℕ → ℝ} {C : ℝ}
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k)
    (hv : Tendsto v atTop atTop)
    (hg : ∀ k, 0 ≤ tk k → v k ≤ C * (1 + tk k)) :
    Tendsto tk atTop atTop := by
  apply tendsto_atTop.2
  intro T
  have hB : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  filter_upwards [ht, (tendsto_atTop.1 hv) (max C 1 * (1 + max T 0) + 1)] with k hk hvk
  by_contra hn
  have htk : tk k < T := lt_of_not_ge hn
  have hgk := (hg k hk).trans
    (mul_le_mul_of_nonneg_right (le_max_left C 1) (by linarith))
  have hm : max C 1 * (1 + tk k) < max C 1 * (1 + max T 0) :=
    mul_lt_mul_of_pos_left (by linarith [le_max_left T 0]) hB
  linarith

/-- Same original tk and rho, using the bound in the actual LocalizedFlow. -/
theorem models_physical_time_cofinal {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {h : Flow X} {U P ρ : STF X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {d : ℕ} {hm Cd Dg : ℝ}
    {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hf : FlowStage X o h U P ρ)
    (hp : PolynomialModels X o ρ F d hm Cd Dg tk H Hinv G Ginv)
    (ht : ∀ᶠ k in atTop, 0 ≤ tk k) : Tendsto tk atTop atTop := by
  rcases hf.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hgrowth, _⟩
  obtain ⟨C, hC⟩ := hgrowth o
  exact physical_time_cofinal ht hp.2.1 (fun k hk => hC (tk k) hk)

theorem eventually_chart_threshold {tk : ℕ → ℝ}
    (ht : Tendsto tk atTop atTop) (T : ℝ) : ∀ᶠ k in atTop, T ≤ tk k :=
  (tendsto_atTop.1 ht) T

/-- This only rejects the forever-negative scalar sequence from the gate;
it supplies neither a full old-U02 countermodel nor a source tuple. -/
theorem negative_sequence_rejected :
    ¬ (∀ᶠ k : ℕ in atTop, 0 ≤ -(1 / ((k : ℝ) + 1))) := by
  intro h
  obtain ⟨k, hk⟩ := h.exists
  have hp : 0 < 1 / ((k : ℝ) + 1) := by positivity
  linarith

/-- Genuine late macro endpoints of the ORIGINAL model. Every later absolute
macro index retains a witness past any fixed finite prefix. No arbitrary tail
is claimed to satisfy the model's starting equality. -/
theorem original_macro_coverage_late {n : ℕ} {X : KahlerManifold n} {o : Pt X}
    {ρ : STF X} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {d : ℕ} {hm Cd Dg : ℝ} {tk : ℕ → ℝ} {H Hinv G Ginv : ℕ → PolyMap n}
    (hp : PolynomialModels X o ρ F d hm Cd Dg tk H Hinv G Ginv)
    (hhm : 0 < hm) (K : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∃ k : ℕ,
      K ≤ k ∧ ρ o (tk k) = Real.exp (hm * j) := by
  obtain ⟨j₀, c₁, C₁, _hc₁, _hstart, hcover, _hspacing⟩ := hp.2.2.1
  have hS : Tendsto (fun j : ℕ => Real.exp (hm * (j : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hhm)
  have havoid : ∀ᶠ j : ℕ in atTop,
      ∀ k : Fin K, ρ o (tk k) < Real.exp (hm * j) := by
    apply eventually_all.2
    intro k
    filter_upwards [(tendsto_atTop.1 hS) (ρ o (tk k) + 1)] with j hj
    linarith
  obtain ⟨J, hJ⟩ := eventually_atTop.1 havoid
  refine ⟨max j₀ J, ?_⟩
  intro j hj
  obtain ⟨k, hk⟩ := hcover j ((le_max_left j₀ J).trans hj)
  change ρ o (tk k) = Real.exp (hm * j) at hk
  have hK : K ≤ k := by
    by_contra hn
    have hh := hJ j ((le_max_right j₀ J).trans hj) ⟨k, by omega⟩
    change ρ o (tk k) < Real.exp (hm * j) at hh
    rw [hk] at hh
    exact (lt_irrefl _) hh
  exact ⟨k, hK, hk⟩

#print U02
#print axioms same_clock_gate
#print axioms physical_time_cofinal
#print axioms models_physical_time_cofinal
#print axioms eventually_chart_threshold
#print axioms original_macro_coverage_late
#print axioms negative_sequence_rejected
end Yau.Blueprint.U02SourceScope
