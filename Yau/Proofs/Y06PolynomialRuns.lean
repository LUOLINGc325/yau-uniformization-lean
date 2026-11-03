import Yau.Proofs.Y06FiniteCompletion
import Yau.Proofs.Y06MaskRuns

/-! Assemble the literal finite construction, its common bound, volume
completion and four-family compactness into the full original run predicate. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open scoped Topology

variable {n d : ℕ}

theorem polynomial_runs_of_budgets (hd : 1 ≤ d) (hY02 : VolumeJets n d)
    (aDiag : ℕ → Fin n → ℂ) (haDiag : ∀ k i, aDiag k i ≠ 0)
    (J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (P : ℕ → PolyMap n)
    (reg : ℕ → Prop) (s a : ℕ → ℝ) (k₀ : ℕ) {A L : ℝ}
    (hA : (n + 1 : ℝ) ≤ A) (hL : 0 ≤ L) (hs : ∀ k, 1 ≤ s k)
    (ha : ∀ k, 0 ≤ a k) (halim : Tendsto a atTop (𝓝 0))
    (hstep : ∀ k, reg k → Real.sqrt (s (k + 1)) ≤ Real.sqrt (s k) + L)
    (hP0 : ∀ k, (P k).FixesZero)
    (hPD : ∀ k, (P k).linearPart = Matrix.diagonal (aDiag k))
    (hPCV : ∀ k, reg k → IsConstantVolumeJet (P k) d)
    (hJunit : ∀ k, reg k → IsUnit (J k))
    (hw : ∀ k, reg k → ∀ i, 1 ≤ w k i)
    (hbudget : ∀ k, k₀ ≤ k → reg k →
      polySize (P k) ≤ Real.exp (A * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (J k)) ≤ Real.exp (A * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (J k)⁻¹) ≤ Real.exp (A * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (Matrix.diagonal (aDiag k))) ≤ Real.exp (A * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (Matrix.diagonal (aDiag k))⁻¹) ≤ Real.exp (A * Real.sqrt (s k)))
    (hT : ∀ m, 2 ≤ m → m ≤ d → ∀ k, k₀ ≤ k → reg k →
      ∀ X : PolyMap n, Homogeneous X m →
        (backwardOperator (Matrix.diagonal (aDiag k)) (J k) (w k) X).coeffNorm ≤ a k * X.coeffNorm) :
    ∃ K : ℕ, k₀ ≤ K ∧ RegularJetRuns (fun k => (P k).eval)
      (fun k => Matrix.diagonal (aDiag k)) J w (fun k => K ≤ k ∧ reg k) d (d ^ (n + 1)) s := by
  obtain ⟨K, hK, E, hE, hfiniteSize⟩ := uniform_finite_stage_bound hd aDiag haDiag J w P reg
    (fun k => Real.sqrt (s k)) a k₀ hA hL (fun k => Yau.Proofs.Y01Aux.sqrt_one_le (hs k)) ha halim
    hstep hP0 hPD hJunit hbudget hT
  obtain ⟨Dd, C, hrealize⟩ := hY02
  have hA0 : 0 ≤ A := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hC : 0 < completionConstant n d C E A := by
    dsimp [completionConstant, inverseJetEnvelopeExponent, inverseModelEnvelopeExponent]
    positivity
  refine ⟨K, hK, regularJetRuns_of_uniform_finite_masks P (fun k => Matrix.diagonal (aDiag k))
    J w (fun k => K ≤ k ∧ reg k) s (completionConstant n d C E A) hC (d ^ (n + 1)) ?_⟩
  intro b active hactive
  have hact : ∀ k, active k → K ≤ k ∧ reg k ∧ k < b :=
    fun k hk => ⟨(hactive k hk).1.1, (hactive k hk).1.2, (hactive k hk).2⟩
  let Q₀ := finiteJetStage b active (fun k => Matrix.diagonal (aDiag k)) J w P (d - 1)
  have hSpec : FiniteStageSpec active (fun k => Matrix.diagonal (aDiag k)) J w P Q₀.1 Q₀.2 d := by
    have h := finiteJetStage_spec b active aDiag haDiag J (fun k hk => hJunit k (hact k hk).2.1)
      w P hP0 hPD (fun k hk => (hact k hk).2.2) (d - 1)
    simpa only [Nat.sub_add_cancel hd] using h
  have hCV : ∀ k, IsConstantVolumeJet (Q₀.1 k) d :=
    finiteStage_correction_volume b (fun k hk => (hact k hk).2.2) haDiag hd
      (fun k hk => hPCV k (hact k hk).2.1) hSpec (fun k hk => hw k (hact k hk).2.1)
  obtain ⟨Q, hQ, hQH, hQG, hdegree, hbound⟩ := complete_finite_stage hrealize hd hE hA0 s hs
    active aDiag haDiag J w P Q₀.1 Q₀.2 hSpec hCV (fun k hk => hw k (hact k hk).2.1)
    (hfiniteSize b active hact)
    (fun k hk => (hbudget k (hK.trans (hact k hk).1) (hact k hk).2.1).2.2.2.2)
  exact ⟨Q, hQ, hdegree, hbound⟩

end Yau.Proofs.Y06Aux
