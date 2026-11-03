import spec.CHAIN.CONTRACTS

noncomputable section
namespace Yau.Blueprint.C02Proof

def finiteJetEnvelope (b : ℕ → ℝ) (m : ℕ) : ℝ :=
  1 + ∑ j : Fin (m + 1), |b j|

theorem finiteJetEnvelope_one_le (b : ℕ → ℝ) (m : ℕ) : 1 ≤ finiteJetEnvelope b m := by
  have hh : 0 ≤ ∑ j : Fin (m + 1), |b j| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  dsimp only [finiteJetEnvelope]
  linarith

theorem le_finiteJetEnvelope (b : ℕ → ℝ) {i m : ℕ} (hi : i ≤ m) : b i ≤ finiteJetEnvelope b m := by
  have hh : |b i| ≤ ∑ j : Fin (m + 1), |b j| :=
    Finset.single_le_sum (f := fun j : Fin (m + 1) => |b j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ (⟨i, by omega⟩ : Fin (m + 1)))
  dsimp only [finiteJetEnvelope]
  linarith [le_abs_self (b i)]

theorem le_finiteJetEnvelope_pow (b : ℕ → ℝ) {i m : ℕ} (hi : 1 ≤ i) (him : i ≤ m) :
    b i ≤ finiteJetEnvelope b m ^ i :=
  (le_finiteJetEnvelope b him).trans
    (le_self_pow₀ (finiteJetEnvelope_one_le b m) (by omega))

end Yau.Blueprint.C02Proof
