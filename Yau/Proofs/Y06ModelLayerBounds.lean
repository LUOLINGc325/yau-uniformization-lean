import Yau.Proofs.Y06StageEstimates

/-! The allowed layer is bounded by finite polynomial composition;
only the forbidden correction uses contraction. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n d : ℕ}

theorem finiteLayerModel_size (b : ℕ) (active : ℕ → Prop)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (B : ℕ → PolyMap n) (k : ℕ)
    {A F H L x : ℝ} (hk : active k)
    (hUdegree : (finiteLayerCorrection b active D J w B (k + 1)).degree ≤ d)
    (hU : polySize (finiteLayerCorrection b active D J w B (k + 1)) ≤
      Real.exp (((H + 1) * (1 + L)) * x))
    (hJ : polySize (linearPolynomial (J k)) ≤ Real.exp (A * x))
    (hJi : polySize (linearPolynomial (J k)⁻¹) ≤ Real.exp (A * x))
    (hD : polySize (linearPolynomial (D k)) ≤ Real.exp (A * x))
    (hB : polySize (B k) ≤ Real.exp (F * x)) :
    polySize (finiteLayerModel b active D J w B k) ≤
      Real.exp ((((H + 1) * (1 + L)) + (2 * (d : ℝ) + 1) * A + F) * x) := by
  classical
  have hJD : polySize (linearPolynomial (J k * D k)) ≤ Real.exp ((2 * A) * x) := by
    have h := polySize_exp_comp (linearPoly_degree_le (J k)) hJ hD
    simp only [linearPolynomial_as_linearPoly, linearPoly_comp,
      Nat.cast_one, one_mul, ← two_mul] at h ⊢
    exact h
  have hUJD := polySize_exp_comp hUdegree hU hJD
  have hleft := polySize_exp_comp (linearPoly_degree_le (J k)⁻¹) hJi hUJD
  have hZ := polySize_exp_add hleft hB
  rw [finiteLayerModel, if_pos hk]
  apply (polySize_allowedProjection _ _).trans
  change polySize ((linearPolynomial (J k)⁻¹).comp
    ((finiteLayerCorrection b active D J w B (k + 1)).comp (linearPolynomial (J k * D k))) + B k) ≤ _
  convert hZ using 1 <;> congr 1 <;> push_cast <;> ring

def stageExponent (d : ℕ) (A L : ℝ) : ℕ → ℝ
  | 0 => A
  | r + 1 =>
    let E := stageExponent d A L r
    let B := ((d : ℝ) + 2 + L) * E + (2 * (d : ℝ) + 1) * A
    let F := B + A
    let H := F + 1
    let G := (H + 1) * (1 + L) + (2 * (d : ℝ) + 1) * A + B
    E + max (H + 1) G

def stageForcingExponent (d : ℕ) (A L : ℝ) (r : ℕ) : ℝ :=
  ((d : ℝ) + 2 + L) * stageExponent d A L r + (2 * (d : ℝ) + 1) * A + A

theorem stageExponent_nonneg (d : ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∀ r, 0 ≤ stageExponent d A L r := by
  intro r
  induction r with
  | zero => exact hA
  | succ r ih =>
    dsimp only [stageExponent]
    positivity

theorem stageForcingExponent_nonneg (d : ℕ) {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (r : ℕ) :
    0 ≤ stageForcingExponent d A L r := by
  dsimp only [stageForcingExponent]
  have hE := stageExponent_nonneg d hA hL r
  positivity

theorem finite_stage_threshold {a : ℕ → ℝ} (ha : Filter.Tendsto a Filter.atTop (nhds 0))
    (d : ℕ) (A L : ℝ) :
    ∃ K : ℕ, ∀ k, K ≤ k → ∀ r < d,
      a k * Real.exp ((stageForcingExponent d A L r + 1) * L) ≤ 1 / 2 := by
  have hall (count : ℕ) : ∃ K : ℕ, ∀ k, K ≤ k → ∀ r < count,
      a k * Real.exp ((stageForcingExponent d A L r + 1) * L) ≤ 1 / 2 := by
    induction count with
    | zero => exact ⟨0, by intro k hk r hr; omega⟩
    | succ count ih =>
      obtain ⟨K, hK⟩ := ih
      have hlim := ha.mul_const (Real.exp ((stageForcingExponent d A L count + 1) * L))
      have hsmall : ∀ᶠ k in Filter.atTop,
          a k * Real.exp ((stageForcingExponent d A L count + 1) * L) ≤ 1 / 2 := by
        apply ((tendsto_order.mp hlim).2 (1 / 2) (by norm_num)).mono
        intro k hk
        exact hk.le
      obtain ⟨Knew, hKnew⟩ := Filter.eventually_atTop.mp hsmall
      refine ⟨max K Knew, ?_⟩
      intro k hk r hr
      by_cases heq : r = count
      · subst r
        exact hKnew k ((le_max_right _ _).trans hk)
      · exact hK k ((le_max_left _ _).trans hk) r (by omega)
  exact hall d

end Yau.Proofs.Y06Aux
