import Yau.LeafProofs.L05PucciHarnackDyadicPartition
import Mathlib.Analysis.Normed.Group.Bounded

open Set
open scoped InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- A bounded set meets only finitely many boxes of any fixed grid level. -/
theorem harnack_grid_finite_meeting_bounded {n : ℕ} {h0 : ℝ} (h0pos : 0 < h0) (k : ℕ)
    {E : Set (Point n)} (hE : Bornology.IsBounded E) :
    Set.Finite {ij : (Yau.RIdx n → ℤ) × ℤ | (harnackGridBox h0 k ij.1 ij.2 ∩ E).Nonempty} := by
  obtain ⟨R,hR⟩ := hE.exists_norm_le
  let r := harnackGridSide h0 k
  have hr : 0 < r := harnack_grid_side_pos h0pos k
  let S : Set (Yau.RIdx n → ℤ) := {i | ∀ q, i q ∈ Icc ⌊-R/r⌋ ⌊R/r⌋}
  let J : Set ℤ := Icc (⌈-R/r^2⌉-1) (⌈R/r^2⌉-1)
  have hS : S.Finite := Set.Finite.pi' (fun _ => Set.finite_Icc _ _)
  have hJ : J.Finite := Set.finite_Icc _ _
  apply (hS.prod hJ).subset
  intro ij hij
  obtain ⟨p,hpBox,hpE⟩ := hij
  have hpNorm := hR p hpE
  obtain ⟨hIndices,hTime⟩ := (harnack_grid_box_mem_iff h0pos k ij.1 ij.2 p).mp hpBox
  have hSpace : ‖p.1‖ ≤ R := (norm_fst_le p).trans hpNorm
  have hTimeBound : |p.2| ≤ R := (show |p.2| ≤ ‖p‖ from norm_snd_le p).trans hpNorm
  refine ⟨?_,?_⟩
  · intro q
    have hVec : ‖Yau.realVec q‖=1 := by
      simpa only [complexVector_realOrthonormalBasis_apply] using
        (complexVector_realOrthonormalBasis n).orthonormal.norm_eq_one q
    have hCoord : |inner ℝ p.1 (Yau.realVec q)| ≤ R := by
      calc
        _ ≤ ‖p.1‖*‖Yau.realVec q‖ := abs_real_inner_le_norm _ _
        _ ≤ R := by simpa only [hVec,mul_one] using hSpace
    have hLow := Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hCoord).1 hr.le)
    have hHigh := Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp hCoord).2 hr.le)
    rw [hIndices q] at hLow hHigh
    exact ⟨hLow,hHigh⟩
  · have hLow := Int.ceil_mono (div_le_div_of_nonneg_right (abs_le.mp hTimeBound).1 (sq_nonneg r))
    have hHigh := Int.ceil_mono (div_le_div_of_nonneg_right (abs_le.mp hTimeBound).2 (sq_nonneg r))
    change ⌈-R/r^2⌉-1 ≤ ij.2 ∧ ij.2 ≤ ⌈R/r^2⌉-1
    rw [← hTime]
    exact ⟨sub_le_sub_right hLow 1,sub_le_sub_right hHigh 1⟩

end Yau.LeafProofs.L05Aux
