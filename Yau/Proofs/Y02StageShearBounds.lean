import Yau.Proofs.Y02QuantitativeFold
import Yau.Proofs.Y02FixedShears

/-! Fixed stage bounds for every parameter in one homogeneous correction. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem firstDiscrepancy_stage_bound (m E : ℕ) (hE : 1 ≤ E) (K : ℝ)
    (P G Ginv : PolyMap n)
    (hbound : G.coeffNorm + Ginv.coeffNorm ≤ K * (1 + P.coeffNorm) ^ E) :
    (firstDiscrepancy m P G).coeffNorm ≤ (1 + K) * (1 + P.coeffNorm) ^ E := by
  have ht : 1 ≤ 1 + P.coeffNorm := by linarith [coeffNorm_nonneg P]
  have hpow : 1 + P.coeffNorm ≤ (1 + P.coeffNorm) ^ E := by
    simpa only [pow_one] using pow_le_pow_right₀ ht hE
  have hG : G.coeffNorm ≤ K * (1 + P.coeffNorm) ^ E := by
    linarith [coeffNorm_nonneg Ginv]
  calc
    _ ≤ P.coeffNorm + G.coeffNorm := firstDiscrepancy_norm_le _ _ _
    _ ≤ (1 + P.coeffNorm) ^ E + K * (1 + P.coeffNorm) ^ E := add_le_add (by linarith) hG
    _ = _ := by ring

theorem stage_shear_bounds {N : ℕ} (l v : Fin N → Fin n → ℂ) (m E : ℕ)
    (c : Fin N → ℂ) (Cm K t : ℝ) (hCm : 0 ≤ Cm) (hK : 0 ≤ K) (ht : 1 ≤ t)
    (hc : (∑ i, ‖c i‖) ≤ Cm * (1 + K) * t ^ E) :
    let B := ∑ i, (shearField (l i) (v i) m).coeffNorm
    let a := (n : ℝ) + 1 + B * Cm * (1 + K)
    1 ≤ a ∧ ∀ i,
      (shear (l i) (v i) m (c i)).coeffNorm ≤ a * t ^ E ∧
        (shear (l i) (v i) m (-c i)).coeffNorm ≤ a * t ^ E := by
  classical
  let B := ∑ i, (shearField (l i) (v i) m).coeffNorm
  let a := (n : ℝ) + 1 + B * Cm * (1 + K)
  have hBn : 0 ≤ B :=
    Finset.sum_nonneg fun i hi => coeffNorm_nonneg (shearField (l i) (v i) m)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have htn : 0 ≤ t := zero_le_one.trans ht
  have hp : 1 ≤ t ^ E := one_le_pow₀ ht
  have ha : 1 ≤ a := by
    have hz : 0 ≤ B * Cm * (1 + K) := mul_nonneg (mul_nonneg hBn hCm) (by linarith)
    dsimp [a]
    linarith only [hz, hn0]
  refine ⟨ha, ?_⟩
  intro i
  have hci : ‖c i‖ ≤ Cm * (1 + K) * t ^ E :=
    (Finset.single_le_sum (fun j hj => norm_nonneg (c j)) (Finset.mem_univ i)).trans hc
  have hfield : (shearField (l i) (v i) m).coeffNorm ≤ B :=
    Finset.single_le_sum (fun j hj => coeffNorm_nonneg (shearField (l j) (v j) m)) (Finset.mem_univ i)
  have hbound (x : ℂ) (hx : ‖x‖ ≤ Cm * (1 + K) * t ^ E) :
      (shear (l i) (v i) m x).coeffNorm ≤ a * t ^ E := by
    apply (shear_coeffNorm_le (l i) (v i) m x).trans
    have hproduct : ‖x‖ * (shearField (l i) (v i) m).coeffNorm ≤
        (Cm * (1 + K) * t ^ E) * B :=
      mul_le_mul hx hfield (coeffNorm_nonneg (shearField (l i) (v i) m)) (by positivity)
    apply (add_le_add le_rfl hproduct).trans
    have hn : (n : ℝ) ≤ (n : ℝ) * t ^ E := le_mul_of_one_le_right hn0 hp
    dsimp [a]
    calc
      _ = (n : ℝ) + (B * Cm * (1 + K)) * t ^ E := by ring
      _ ≤ (n : ℝ) * t ^ E + (B * Cm * (1 + K)) * t ^ E := add_le_add hn le_rfl
      _ = ((n : ℝ) + B * Cm * (1 + K)) * t ^ E := by ring
      _ ≤ ((n : ℝ) + 1 + B * Cm * (1 + K)) * t ^ E :=
        mul_le_mul_of_nonneg_right (by linarith only []) (zero_le_one.trans hp)
  exact ⟨hbound (c i) hci, hbound (-c i) (by simpa only [norm_neg] using hci)⟩

end Yau.Proofs.Y02Aux
