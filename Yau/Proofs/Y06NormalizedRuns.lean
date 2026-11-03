import Yau.Proofs.Y06PolynomialRuns
import Yau.Proofs.Y06NormalizedData

/-! The complete homological construction uses the original normalized
transition and its actual same-degree polynomial jet on regular indices. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux
open scoped Topology ContDiff

variable {n d : ℕ}

theorem normalized_runs_of_budgets
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk s : ℕ → ℝ} {Eframes : Frames n}
    (hE : SingularFrames F tk Eframes) {r : ℝ} {last : Fin n} {logs : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell Evol : ℕ → MvPolynomial (Fin n) ℂ}
    {A Ainv V : ℕ → PolyMap n}
    (hVol : CoherentVolume F tk s d r last logs B ell Evol A Ainv V) (hd : 1 ≤ d)
    (hY02 : VolumeJets n d)
    (hF : ∀ k, F (tk k) (tk (k + 1)) 0 = 0 ∧
      DifferentiableOn ℂ (F (tk k) (tk (k + 1))) (Metric.ball 0 r))
    {L : Changes n} {w : ℕ → Fin n → ℝ} {j : ℕ → ℕ} {S : ℕ → ℝ} {CL cL : ℝ}
    {reg : ℕ → Prop} (hL : ∀ k, reg k → ChangeAt (diagonal F tk Eframes) w j S CL cL L k)
    (J : ℕ → Herm n) (a : ℕ → ℝ) (k₀ : ℕ) {Ab Lb : ℝ}
    (hAb : (n + 1 : ℝ) ≤ Ab) (hLb : 0 ≤ Lb) (hs : ∀ k, 1 ≤ s k)
    (ha : ∀ k, 0 ≤ a k) (halim : Tendsto a atTop (𝓝 0))
    (hstep : ∀ k, reg k → Real.sqrt (s (k + 1)) ≤ Real.sqrt (s k) + Lb)
    (hJunit : ∀ k, reg k → IsUnit (J k)) (hw : ∀ k, reg k → ∀ i, 1 ≤ w k i)
    (hbudget : ∀ k, k₀ ≤ k → reg k →
      polySize (normalizedPolynomial V Eframes L k) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (J k)) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (J k)⁻¹) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (diagonal F tk Eframes k)) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (diagonal F tk Eframes k)⁻¹) ≤ Real.exp (Ab * Real.sqrt (s k)))
    (hT : ∀ m, 2 ≤ m → m ≤ d → ∀ k, k₀ ≤ k → reg k →
      ∀ X : PolyMap n, Homogeneous X m →
        (backwardOperator (diagonal F tk Eframes k) (J k) (w k) X).coeffNorm ≤ a k * X.coeffNorm) :
    ∃ K : ℕ, k₀ ≤ K ∧ RegularJetRuns (normalizedRegularTransition F tk A Ainv Eframes L)
      (diagonal F tk Eframes) J w (fun k => K ≤ k ∧ reg k) d (d ^ (n + 1)) s := by
  classical
  let P := fun k => if reg k then normalizedPolynomial V Eframes L k else linearPolynomial (diagonal F tk Eframes k)
  let aDiag := fun k i => (singularLength F tk Eframes k i : ℂ)
  have haDiag : ∀ k i, aDiag k i ≠ 0 := fun k i =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt ((hE k).2.2.2.2.2.1 i).1)
  have hdata := normalizedRegularTransition_data hE hVol hd hF hL
  have hP0 : ∀ k, (P k).FixesZero := by
    intro k
    by_cases hk : reg k
    · rw [show P k = normalizedPolynomial V Eframes L k from ite_eq_left hk]
      exact (hdata k hk).1.1
    · rw [show P k = linearPolynomial (diagonal F tk Eframes k) from ite_eq_right hk]
      exact linearPoly_fixesZero _
  have hPD : ∀ k, (P k).linearPart = Matrix.diagonal (aDiag k) := by
    intro k
    by_cases hk : reg k
    · rw [show P k = normalizedPolynomial V Eframes L k from ite_eq_left hk]
      exact (hdata k hk).2.1
    · rw [show P k = linearPolynomial (diagonal F tk Eframes k) from ite_eq_right hk]
      exact linearPoly_linearPart _
  have hPCV : ∀ k, reg k → IsConstantVolumeJet (P k) d := by
    intro k hk
    rw [show P k = normalizedPolynomial V Eframes L k from ite_eq_left hk]
    exact (hdata k hk).1
  have hbudget' : ∀ k, k₀ ≤ k → reg k →
      polySize (P k) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (J k)) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (J k)⁻¹) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (Matrix.diagonal (aDiag k))) ≤ Real.exp (Ab * Real.sqrt (s k)) ∧
      polySize (linearPolynomial (Matrix.diagonal (aDiag k))⁻¹) ≤ Real.exp (Ab * Real.sqrt (s k)) := by
    intro k hk hreg
    rw [show P k = normalizedPolynomial V Eframes L k from ite_eq_left hreg]
    exact hbudget k hk hreg
  obtain ⟨K, hK, hruns⟩ := polynomial_runs_of_budgets hd hY02 aDiag haDiag J w P reg s a k₀ hAb hLb hs
    ha halim hstep hP0 hPD hPCV hJunit hw hbudget' hT
  refine ⟨K, hK, regularJetRuns_transport ?_ hruns⟩
  intro k hk
  have hPactual : P k = normalizedPolynomial V Eframes L k := ite_eq_left hk.2
  have hPcont : ContDiffAt ℂ d (P k).eval 0 :=
    (polyMap_eval_contDiff _).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  exact ⟨hPcont, (hdata k hk.2).2.2.2.1, (fixesZero_iff_eval_zero _).mp (hP0 k),
    (hdata k hk.2).2.2.2.2, by rw [hPactual]; exact (hdata k hk.2).2.2.1⟩

end Yau.Proofs.Y06Aux
