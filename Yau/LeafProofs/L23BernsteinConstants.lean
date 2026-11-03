import Yau.LeafProofs.L23BernsteinAlgebra

/-! Numerical constants are selected before any manifold or metric family. -/

noncomputable section

namespace Yau.LeafProofs.L23Aux

def derivativeWeight (k : ℕ) : ℝ := (1/2 : ℝ)^k
def derivativeRadius (r : ℝ) (k : ℕ) : ℝ := r*(1+derivativeWeight k)
def derivativeTimeOffset (τ : ℝ) (k : ℕ) : ℝ := τ*(1-derivativeWeight k)
def derivativeCutoffRadius (n : ℕ) (K r τ σ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-σ*(2*n : ℕ)*K*τ)*r*derivativeWeight k/4
def derivativeTimeBuffer (τ : ℝ) (k : ℕ) : ℝ := τ*derivativeWeight k

theorem derivativeWeight_pos (k : ℕ) : 0 < derivativeWeight k := by
  unfold derivativeWeight
  positivity

theorem derivativeWeight_le_one (k : ℕ) : derivativeWeight k ≤ 1 := by
  induction k with
  | zero => norm_num [derivativeWeight]
  | succ k ih =>
      have hp := derivativeWeight_pos k
      simp only [derivativeWeight,pow_succ] at *
      nlinarith

theorem derivativeRadius_zero (r : ℝ) : derivativeRadius r 0=2*r := by
  simp only [derivativeRadius,derivativeWeight,pow_zero]
  ring

theorem derivativeTimeOffset_zero (τ : ℝ) : derivativeTimeOffset τ 0=0 := by
  simp [derivativeTimeOffset,derivativeWeight]

theorem lt_derivativeRadius {r : ℝ} (hr : 0 < r) (k : ℕ) : r < derivativeRadius r k := by
  have hp := mul_pos hr (derivativeWeight_pos k)
  dsimp only [derivativeRadius]
  linarith

theorem derivativeTimeOffset_lt {τ : ℝ} (hτ : 0 < τ) (k : ℕ) : derivativeTimeOffset τ k < τ := by
  have hp := mul_pos hτ (derivativeWeight_pos k)
  dsimp only [derivativeTimeOffset]
  linarith

theorem derivativeRadius_difference (r : ℝ) (k : ℕ) :
    derivativeRadius r k-derivativeRadius r (k+1)=r*derivativeWeight (k+1) := by
  simp only [derivativeRadius,derivativeWeight,pow_succ]
  ring

theorem derivativeTimeOffset_difference (τ : ℝ) (k : ℕ) :
    derivativeTimeOffset τ (k+1)-derivativeTimeOffset τ k=derivativeTimeBuffer τ (k+1) := by
  simp only [derivativeTimeOffset,derivativeTimeBuffer,derivativeWeight,pow_succ]
  ring

theorem derivativeRadius_antitone {r : ℝ} (hr : 0 < r) : Antitone (derivativeRadius r) := by
  apply antitone_nat_of_succ_le
  intro k
  have hh := derivativeRadius_difference r k
  have hp := mul_pos hr (derivativeWeight_pos (k+1))
  linarith

theorem derivativeTimeOffset_monotone {τ : ℝ} (hτ : 0 < τ) : Monotone (derivativeTimeOffset τ) := by
  apply monotone_nat_of_le_succ
  intro k
  have hh := derivativeTimeOffset_difference τ k
  have hp : 0 < derivativeTimeBuffer τ (k+1) := mul_pos hτ (derivativeWeight_pos _)
  linarith

theorem derivativeCutoffRadius_pos (n : ℕ) (K r τ σ : ℝ) (hr : 0 < r) (k : ℕ) :
    0 < derivativeCutoffRadius n K r τ σ k := by
  unfold derivativeCutoffRadius
  exact div_pos (mul_pos (mul_pos (Real.exp_pos _) hr) (derivativeWeight_pos _)) (by norm_num)

theorem derivativeTimeBuffer_pos {τ : ℝ} (hτ : 0 < τ) (k : ℕ) :
    0 < derivativeTimeBuffer τ k := mul_pos hτ (derivativeWeight_pos _)

def bernsteinStepBound (n k : ℕ) (K σ R δ B ccur cprev : ℝ) : ℝ :=
  let A := 16*B
  let P := 17*B
  let Dk := ccur*(k+1)*B
  let Ek := cprev*k*B^2
  let α := 1/(4*P^2)
  let β := (P*Dk+Ek)^2+P*Dk
  let Λ := σ*(2*(2*n : ℕ)/R^2+(8/3 : ℝ)*(2*n : ℕ)*K)+σ*(16/R^2)
  1+(2*(1+Λ*δ)/(σ*α*δ)+Real.sqrt (2*β/α))/A

theorem bernsteinStepBound_pos (n k : ℕ) (K σ R δ B ccur cprev : ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hR : 0 < R) (hδ : 0 < δ)
    (hB : 1 ≤ B) (hcur : 0 < ccur) (hprev : 0 < cprev) :
    0 < bernsteinStepBound n k K σ R δ B ccur cprev := by
  have hBpos : 0 < B := by linarith
  unfold bernsteinStepBound
  positivity

def bernsteinNumericState (n : ℕ) (K σ : ℝ) (R δ c : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (K^2,K^2)
  | k+1 =>
      let old := bernsteinNumericState n K σ R δ c k
      let N := bernsteinStepBound n (k+1) K σ (R (k+1)) (δ (k+1))
        (1+old.2) (c (k+1)) (c k)
      (N,old.2+N)

def bernsteinNumericBound (n : ℕ) (K σ : ℝ) (R δ c : ℕ → ℝ) (k : ℕ) : ℝ :=
  (bernsteinNumericState n K σ R δ c k).1

theorem bernsteinNumericState_pos (n : ℕ) (K σ : ℝ) (R δ c : ℕ → ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hR : ∀ k, 0 < R k)
    (hδ : ∀ k, 0 < δ k) (hc : ∀ k, 0 < c k) (k : ℕ) :
    0 < (bernsteinNumericState n K σ R δ c k).1 ∧
      0 ≤ (bernsteinNumericState n K σ R δ c k).2 := by
  induction k with
  | zero => simp only [bernsteinNumericState]; constructor <;> positivity
  | succ k ih =>
      have hB : 1 ≤ 1+(bernsteinNumericState n K σ R δ c k).2 := by linarith [ih.2]
      have hnew := bernsteinStepBound_pos n (k+1) K σ (R (k+1)) (δ (k+1))
        (1+(bernsteinNumericState n K σ R δ c k).2) (c (k+1)) (c k)
        hK hσ (hR _) (hδ _) hB (hc _) (hc _)
      exact ⟨hnew,add_nonneg ih.2 hnew.le⟩

theorem bernsteinNumericBound_sum (n : ℕ) (K σ : ℝ) (R δ c : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ Finset.range (k+1), bernsteinNumericBound n K σ R δ c i) =
      (bernsteinNumericState n K σ R δ c k).2 := by
  induction k with
  | zero => simp [bernsteinNumericBound,bernsteinNumericState]
  | succ k ih =>
      rw [Finset.sum_range_succ,ih]
      rfl

theorem bernsteinNumericBound_le_total (n : ℕ) (K σ : ℝ) (R δ c : ℕ → ℝ)
    (hK : 0 < K) (hσ : 0 < σ) (hR : ∀ k, 0 < R k)
    (hδ : ∀ k, 0 < δ k) (hc : ∀ k, 0 < c k) {i k : ℕ} (hik : i ≤ k) :
    bernsteinNumericBound n K σ R δ c i ≤ (bernsteinNumericState n K σ R δ c k).2 := by
  rw [←bernsteinNumericBound_sum]
  exact Finset.single_le_sum
    (fun j _ => (bernsteinNumericState_pos n K σ R δ c hK hσ hR hδ hc j).1.le)
    (by simp only [Finset.mem_range]; omega)

end Yau.LeafProofs.L23Aux
