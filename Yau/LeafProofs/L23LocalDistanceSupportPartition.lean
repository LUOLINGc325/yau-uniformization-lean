import Yau.LeafProofs.L23LocalDistanceSupportSegments

/-! Equal cumulative-length samples, with genuine ordered unit-interval parameters. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
set_option maxHeartbeats 600000

theorem exists_equal_primitive_samples (L : ℝ → ℝ)
    (hL : ContinuousOn L (Set.Icc (0 : ℝ) 1))
    (hmono : MonotoneOn L (Set.Icc (0 : ℝ) 1))
    (hzero : L 0 = 0) (hpos : 0 < L 1) (N : ℕ) :
    ∃ t : Fin (N+2) → ℝ, t 0 = 0 ∧ t (Fin.last (N+1)) = 1 ∧
      (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) ∧ StrictMono t ∧
      ∀ i, L (t i) = (i.val : ℝ)/(N+1 : ℕ)*L 1 := by
  have hN : (0 : ℝ) < (N+1 : ℕ) := by positivity
  have hex : ∀ i : Fin N, ∃ u ∈ Set.Icc (0 : ℝ) 1,
      L u = (i.val+1 : ℕ)/(N+1 : ℕ)*L 1 := by
    intro i
    apply intermediate_value_Icc zero_le_one hL
    rw [hzero]
    refine ⟨by positivity,?_⟩
    have Hrat : ((i.val+1 : ℕ) : ℝ)/(N+1 : ℕ) ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast (Nat.succ_le_succ i.isLt.le))
    exact mul_le_of_le_one_left hpos.le Hrat
  choose u hu huL using hex
  let t : Fin (N+2) → ℝ := Fin.cases 0 (Fin.lastCases 1 u)
  have ht₀ : t 0 = 0 := rfl
  have ht₁ : t (Fin.last (N+1)) = 1 := by
    change Fin.lastCases (motive := fun _ : Fin (N+1) => ℝ) (1 : ℝ) u (Fin.last N) = (1 : ℝ)
    simp
  have hti : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [ht₀]
      exact ⟨le_rfl,zero_le_one⟩
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simpa only [t,Fin.cases_succ,Fin.lastCases_last] using (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
      · simpa only [t,Fin.cases_succ,Fin.lastCases_castSucc] using hu k
  have htL : ∀ i, L (t i) = (i.val : ℝ)/(N+1 : ℕ)*L 1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ht₀,hzero,Fin.val_zero,Nat.cast_zero,zero_div,zero_mul]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [t,Fin.cases_succ,Fin.lastCases_last,Fin.val_succ,Fin.val_last]
        rw [div_self hN.ne',one_mul]
      · simpa only [t,Fin.cases_succ,Fin.lastCases_castSucc,Fin.val_succ,Fin.val_castSucc] using huL k
  refine ⟨t,ht₀,ht₁,hti,?_,htL⟩
  intro i j hij
  by_contra h
  have Hmono := hmono (hti j) (hti i) (le_of_not_gt h)
  rw [htL j,htL i] at Hmono
  have Hcast : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have Hlt := mul_lt_mul_of_pos_right ((div_lt_div_iff_of_pos_right hN).mpr Hcast) hpos
  exact (not_lt_of_ge Hmono) Hlt

end Yau.LeafProofs.L23Aux
