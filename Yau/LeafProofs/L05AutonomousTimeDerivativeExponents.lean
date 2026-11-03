import Yau.LeafProofs.L05AutonomousTimeIncrementsHolder

noncomputable section
open Set
namespace Yau.LeafProofs.L05AutonomousAux

/-- Every scalar reconstruction exponent is strictly below one. -/
def autoTDBeta (delta : ℝ) (j : ℕ) : ℝ :=
  min (delta/2+(j : ℝ)*(delta/4)) (1-delta/4)

theorem auto_td_beta_zero {delta : ℝ} (_hd : 0<delta) (hd1 : delta<1) :
    autoTDBeta delta 0=delta/2 := by
  simp only [autoTDBeta,Nat.cast_zero,zero_mul,add_zero]
  apply min_eq_left
  linarith only [hd1]

theorem auto_td_beta_bounds {delta : ℝ} (hd : 0<delta) (hd1 : delta<1) (j : ℕ) :
    0<autoTDBeta delta j ∧ autoTDBeta delta j<1 := by
  constructor
  · apply lt_min
    · positivity
    · linarith only [hd1]
  · exact (min_le_right _ _).trans_lt (by linarith only [hd])

theorem auto_td_beta_step {delta : ℝ} (hd : 0<delta) (j : ℕ) :
    autoTDBeta delta (j+1)≤autoTDBeta delta j+delta/2 := by
  dsimp only [autoTDBeta]
  by_cases hj : delta/2+(j : ℝ)*(delta/4)≤1-delta/4
  · rw [min_eq_left hj]
    have h := min_le_left (delta/2+((j+1 : ℕ) : ℝ)*(delta/4)) (1-delta/4)
    push_cast at h ⊢
    nlinarith only [h,hd]
  · rw [min_eq_right (le_of_not_ge hj)]
    have h := min_le_right (delta/2+((j+1 : ℕ) : ℝ)*(delta/4)) (1-delta/4)
    linarith only [h,hd]

/-- The number of exponent improvements is finite and depends only on delta. -/
theorem auto_td_beta_eventually {delta : ℝ} (hd : 0<delta) :
    ∃ N : ℕ, autoTDBeta delta N=1-delta/4 := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((1-delta/4-delta/2)/(delta/4))
  refine ⟨N,min_eq_right ?_⟩
  have h := (div_lt_iff₀ (by linarith only [hd] : 0<delta/4)).mp hN
  linarith only [h]

theorem auto_td_final_exponent {delta : ℝ} (hd : 0<delta) (hd1 : delta<1) :
    1<(1-delta/4)+delta/2 ∧ (1-delta/4)+delta/2<2 := by
  constructor <;> linarith only [hd,hd1]

end Yau.LeafProofs.L05AutonomousAux
