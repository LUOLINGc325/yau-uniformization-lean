import Yau.Proofs.Y06RegularLimit

/-! Uniform finite masks yield the global run, every finite interval, and
every infinite tail with one common coefficient subsequence for all four families. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment
open scoped Topology

variable {n d Dstar : ℕ}

theorem regularJetRuns_of_uniform_finite_masks
    (P : ℕ → PolyMap n) (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ)
    (reg : ℕ → Prop) (s : ℕ → ℝ) (C : ℝ) (hC : 0 < C) (Dbound : ℕ)
    (hfinite : ∀ (b : ℕ) (active : ℕ → Prop),
      (∀ k, active k → reg k ∧ k < b) →
      ∃ Q : JetData n,
        RegularJetSolution (fun k => (P k).eval) D J w active d Dstar s C Q ∧
        JetDataDegreeBound Dbound Q ∧
        JetDataNormBound (fun k => Real.exp (C * Real.sqrt (s k))) Q) :
    RegularJetRuns (fun k => (P k).eval) D J w reg d Dstar s := by
  classical
  have hcompact (activeH : ℕ → ℕ → Prop) (active : ℕ → Prop)
      (finite : ℕ → JetData n)
      (hsol : ∀ H, RegularJetSolution (fun k => (P k).eval) D J w (activeH H) d Dstar s C (finite H))
      (hdeg : ∀ H, JetDataDegreeBound Dbound (finite H))
      (hbound : ∀ H, JetDataNormBound (fun k => Real.exp (C * Real.sqrt (s k))) (finite H))
      (hact : ∀ k, ∀ᶠ H in atTop, activeH H k ↔ active k) :
      ∃ (Q : JetData n) (σ : ℕ → ℕ), StrictMono σ ∧
        RegularJetSolution (fun k => (P k).eval) D J w active d Dstar s C Q ∧
        JetDataCoefficientTendsto (fun H => finite (σ H)) Q := by
    obtain ⟨Q, σ, hσ, hQdeg, hlim, hQbound⟩ :=
      jetData_subsequence finite Dbound (fun k => Real.exp (C * Real.sqrt (s k))) hdeg hbound
    refine ⟨Q, σ, hσ, ?_, hlim⟩
    exact regularJetSolution_polynomial_limit P D J w (fun H => activeH (σ H)) active s C
      (fun H => finite (σ H)) Q Dbound (fun H => hdeg (σ H)) hQdeg hlim
      (fun k => hσ.tendsto_atTop.eventually (hact k)) (fun H => hsol (σ H))
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · have hF (H : ℕ) := hfinite (H + 1) (fun k => reg k ∧ k < H + 1) (fun k hk => hk)
    choose finite hsol hdeg hbound using hF
    have hact : ∀ k, ∀ᶠ H in atTop, (reg k ∧ k < H + 1) ↔ reg k := by
      intro k
      filter_upwards [eventually_ge_atTop k] with H hH
      exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
    obtain ⟨Q, σ, hσ, hQ, hlim⟩ := hcompact _ reg finite hsol hdeg hbound hact
    exact ⟨Q, hQ⟩
  · intro a len hlen hreg
    obtain ⟨Q, hQ, hdeg, hbound⟩ := hfinite (a + len) (fun k => a ≤ k ∧ k < a + len)
      (fun k hk => ⟨hreg k hk.1 hk.2, hk.2⟩)
    exact ⟨Q, hQ, (hQ.1 (a + len) (by omega)).1⟩
  · intro a hreg
    have hF (H : ℕ) := hfinite (a + H + 1) (fun k => a ≤ k ∧ k < a + H + 1)
      (fun k hk => ⟨hreg k hk.1, hk.2⟩)
    choose finite hsol hdeg hbound using hF
    have hact : ∀ k, ∀ᶠ H in atTop, (a ≤ k ∧ k < a + H + 1) ↔ a ≤ k := by
      intro k
      filter_upwards [eventually_ge_atTop k] with H hH
      exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
    obtain ⟨Q, σ, hσ, hQ, hlim⟩ := hcompact _ (fun k => a ≤ k) finite hsol hdeg hbound hact
    refine ⟨Q, finite, σ, hσ, hQ, ?_, ?_⟩
    · intro H
      exact ⟨hsol H, ((hsol H).1 (a + H + 1) (by omega)).1⟩
    · intro k i β hk
      exact hlim k i β

end Yau.Proofs.Y06Aux
