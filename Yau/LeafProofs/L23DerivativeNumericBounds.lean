import Yau.LeafProofs.L23BernsteinConstants
import Yau.LeafProofs.L23ContractionWords

/-! All constants for the final jet induction are selected independently of geometry. -/

noncomputable section
namespace Yau.LeafProofs.L23Aux

def localJetBound (n : ℕ) (K r τ σ : ℝ) (k : ℕ) : ℝ :=
  bernsteinNumericBound n K σ (derivativeCutoffRadius n K r τ σ)
    (derivativeTimeBuffer τ) (jetEvolutionConstant n) k

def localJetTotal (n : ℕ) (K r τ σ : ℝ) (k : ℕ) : ℝ :=
  (bernsteinNumericState n K σ (derivativeCutoffRadius n K r τ σ)
    (derivativeTimeBuffer τ) (jetEvolutionConstant n) k).2

theorem localJetBound_zero (n : ℕ) (K r τ σ : ℝ) : localJetBound n K r τ σ 0=K^2 := rfl

theorem localJetBound_succ (n : ℕ) (K r τ σ : ℝ) (k : ℕ) :
    localJetBound n K r τ σ (k+1)=
      bernsteinStepBound n (k+1) K σ (derivativeCutoffRadius n K r τ σ (k+1))
        (derivativeTimeBuffer τ (k+1)) (1+localJetTotal n K r τ σ k)
        (jetEvolutionConstant n (k+1)) (jetEvolutionConstant n k) := rfl

theorem localJetBound_pos (n : ℕ) (K r τ σ : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ) (k : ℕ) :
    0<localJetBound n K r τ σ k :=
  (bernsteinNumericState_pos n K σ _ _ _ hK hσ
    (derivativeCutoffRadius_pos n K r τ σ hr) (derivativeTimeBuffer_pos hτ)
    (jetEvolutionConstant_pos n) k).1

theorem localJetTotal_nonneg (n : ℕ) (K r τ σ : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ) (k : ℕ) :
    0≤localJetTotal n K r τ σ k :=
  (bernsteinNumericState_pos n K σ _ _ _ hK hσ
    (derivativeCutoffRadius_pos n K r τ σ hr) (derivativeTimeBuffer_pos hτ)
    (jetEvolutionConstant_pos n) k).2

theorem localJetBound_le_total (n : ℕ) (K r τ σ : ℝ)
    (hK : 0<K) (hr : 0<r) (hτ : 0<τ) (hσ : 0<σ) {j k : ℕ} (hjk : j≤k) :
    localJetBound n K r τ σ j≤localJetTotal n K r τ σ k :=
  bernsteinNumericBound_le_total n K σ _ _ _ hK hσ
    (derivativeCutoffRadius_pos n K r τ σ hr) (derivativeTimeBuffer_pos hτ)
    (jetEvolutionConstant_pos n) hjk

theorem derivativeRadius_pos {r : ℝ} (hr : 0<r) (k : ℕ) : 0<derivativeRadius r k :=
  hr.trans (lt_derivativeRadius hr k)

theorem derivativeRadius_le_two_mul {r : ℝ} (hr : 0<r) (k : ℕ) :
    derivativeRadius r k≤2*r := by
  have h := derivativeWeight_le_one k
  unfold derivativeRadius
  nlinarith

theorem derivativeRadius_succ_lt {r : ℝ} (hr : 0<r) (k : ℕ) :
    derivativeRadius r (k+1)<derivativeRadius r k := by
  have he := derivativeRadius_difference r k
  have hp := mul_pos hr (derivativeWeight_pos (k+1))
  linarith

theorem derivativeTimeOffset_nonneg {τ : ℝ} (hτ : 0<τ) (k : ℕ) :
    0≤derivativeTimeOffset τ k :=
  mul_nonneg hτ.le (sub_nonneg.mpr (derivativeWeight_le_one k))

theorem derivativeCutoffRadius_eq_buffer (n : ℕ) (K r τ σ : ℝ) (k : ℕ) :
    Real.exp (-σ*(2*n : ℕ)*K*τ)*(derivativeRadius r k-derivativeRadius r (k+1))/4=
      derivativeCutoffRadius n K r τ σ (k+1) := by
  rw [derivativeRadius_difference]
  unfold derivativeCutoffRadius
  ring

end Yau.LeafProofs.L23Aux
