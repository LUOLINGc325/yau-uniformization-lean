import Yau.LeafProofs.L23BernsteinConstants

/-! Uniformly bounded lower jets close the two scalar reaction sums. -/

noncomputable section

namespace Yau.LeafProofs.L23Aux

theorem sqrt_le_one_add {w : ℝ} (hw : 0 ≤ w) : Real.sqrt w ≤ 1+w := by
  nlinarith [Real.sq_sqrt hw,sq_nonneg (Real.sqrt w-(1/2 : ℝ))]

theorem sqrt_le_bound_of_le {u B : ℝ} (hB : 1 ≤ B) (hu : u ≤ B) : Real.sqrt u ≤ B := by
  have hB0 : 0 ≤ B := by linarith
  have hBB : B ≤ B^2 := by nlinarith
  calc
    Real.sqrt u ≤ Real.sqrt (B^2) := Real.sqrt_le_sqrt (hu.trans hBB)
    _ = B := by rw [Real.sqrt_sq_eq_abs,abs_of_nonneg hB0]

theorem sqrt_product_le_bound {u v B : ℝ} (hB : 0 ≤ B) (hu : u ≤ B) (hv : v ≤ B) :
    Real.sqrt u*Real.sqrt v ≤ B := by
  have hm := mul_le_mul (Real.sqrt_le_sqrt hu) (Real.sqrt_le_sqrt hv)
    (Real.sqrt_nonneg v) (Real.sqrt_nonneg B)
  simpa only [←pow_two,Real.sq_sqrt hB] using hm

theorem reaction_sum_le (k : ℕ) (hk : 0 < k) (U : ℕ → ℝ) (B : ℝ)
    (hB : 1 ≤ B) (hU : ∀ j, 0 ≤ U j) (hLower : ∀ j < k, U j ≤ B) :
    (∑ i : Fin (k+1), Real.sqrt (U i.val)*Real.sqrt (U (k-i.val))*Real.sqrt (U k)) ≤
      (k+1 : ℕ)*B*(1+U k) := by
  have hB0 : 0 ≤ B := by linarith
  have hs0 := sqrt_le_bound_of_le hB (hLower 0 hk)
  have hterm (i : Fin (k+1)) :
      Real.sqrt (U i.val)*Real.sqrt (U (k-i.val))*Real.sqrt (U k) ≤ B*(1+U k) := by
    by_cases hi0 : i.val=0
    · rw [hi0,Nat.sub_zero,mul_assoc,←pow_two,Real.sq_sqrt (hU k)]
      calc
        _ ≤ B*U k := mul_le_mul_of_nonneg_right hs0 (hU k)
        _ ≤ _ := by nlinarith
    · by_cases hik : i.val=k
      · rw [hik,Nat.sub_self]
        calc
          Real.sqrt (U k)*Real.sqrt (U 0)*Real.sqrt (U k) =
              Real.sqrt (U 0)*U k := by
            calc
              _ = Real.sqrt (U 0)*(Real.sqrt (U k)*Real.sqrt (U k)) := by ring
              _ = _ := by rw [←pow_two,Real.sq_sqrt (hU k)]
          _ ≤ B*U k := mul_le_mul_of_nonneg_right hs0 (hU k)
          _ ≤ _ := by nlinarith
      · have hi : i.val < k := by omega
        have hki : k-i.val < k := by omega
        have hp := sqrt_product_le_bound hB0 (hLower i.val hi) (hLower (k-i.val) hki)
        calc
          _ ≤ B*Real.sqrt (U k) := mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_le_one_add (hU k)) hB0
  calc
    _ ≤ ∑ i : Fin (k+1), B*(1+U k) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem lower_reaction_sum_le (k : ℕ) (U : ℕ → ℝ) (B : ℝ)
    (hB : 1 ≤ B) (hLower : ∀ j ≤ k, U j ≤ B) :
    (∑ i : Fin (k+1), Real.sqrt (U i.val)*Real.sqrt (U (k-i.val))*Real.sqrt (U k)) ≤
      (k+1 : ℕ)*B^2 := by
  have hB0 : 0 ≤ B := by linarith
  have htop := sqrt_le_bound_of_le hB (hLower k le_rfl)
  have hterm (i : Fin (k+1)) :
      Real.sqrt (U i.val)*Real.sqrt (U (k-i.val))*Real.sqrt (U k) ≤ B^2 := by
    have hi : i.val ≤ k := by omega
    have hp := sqrt_product_le_bound hB0 (hLower i.val hi) (hLower (k-i.val) (Nat.sub_le _ _))
    calc
      _ ≤ B*Real.sqrt (U k) := mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg _)
      _ ≤ B*B := mul_le_mul_of_nonneg_left htop hB0
      _ = _ := by ring
  calc
    _ ≤ ∑ i : Fin (k+1), B^2 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end Yau.LeafProofs.L23Aux
