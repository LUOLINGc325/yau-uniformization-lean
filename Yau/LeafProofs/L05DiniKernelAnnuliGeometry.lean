import Yau.LeafProofs.L05DiniKernelAnnuliIntegrability

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def diniAnnulus {n : ℕ} (R : ℝ) : ℕ → Set (Space n)
  | 0 => {y | ‖y‖ ≤ R}
  | k+1 => {y | (2:ℝ)^k*R < ‖y‖ ∧ ‖y‖ ≤ (2:ℝ)^(k+1)*R}

theorem diniAnnulus_measurable {n : ℕ} (R : ℝ) (k : ℕ) : MeasurableSet (diniAnnulus (n := n) R k) := by
  cases k with
  | zero =>
    change MeasurableSet {y : Space n | ‖y‖ ≤ R}
    exact measurableSet_le measurable_norm measurable_const
  | succ k =>
    change MeasurableSet ({y : Space n | (2:ℝ)^k*R < ‖y‖} ∩ {y : Space n | ‖y‖ ≤ (2:ℝ)^(k+1)*R})
    exact (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)

theorem diniAnnulus_upper {n : ℕ} {R : ℝ} {k : ℕ} {y : Space n} (hy : y ∈ diniAnnulus R k) :
    ‖y‖ ≤ (2:ℝ)^k*R := by
  cases k with
  | zero =>
    simp only [pow_zero,one_mul]
    change ‖y‖ ≤ R at hy
    exact hy
  | succ k => exact hy.2

theorem diniAnnulus_pairwise_disjoint {n : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    Pairwise (fun i j : ℕ => Disjoint (diniAnnulus (n := n) R i) (diniAnnulus R j)) := by
  have hlt (i j : ℕ) (hij : i < j) : Disjoint (diniAnnulus (n := n) R i) (diniAnnulus R j) := by
    apply Set.disjoint_left.mpr
    intro y hyi hyj
    cases j with
    | zero => omega
    | succ k =>
      have hpow : (2:ℝ)^i ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt_succ hij)
      have hscale := mul_le_mul_of_nonneg_right hpow hR
      exact (not_lt_of_ge ((diniAnnulus_upper hyi).trans hscale)) hyj.1
  intro i j hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hlt i j hij
  · exact (hlt j i hji).symm

theorem diniAnnulus_iUnion {n : ℕ} {R : ℝ} (hR : 0 < R) :
    (⋃ k : ℕ, diniAnnulus (n := n) R k)=Set.univ := by
  ext y
  constructor
  · intro hy
    exact Set.mem_univ _
  · intro hy
    have hbig : ∃ k : ℕ, ‖y‖ ≤ (2:ℝ)^k*R := by
      obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (‖y‖/R) (by norm_num : (1:ℝ) < 2)
      exact ⟨k,((div_lt_iff₀ hR).mp hk).le⟩
    let k := Nat.find hbig
    have hk : ‖y‖ ≤ (2:ℝ)^k*R := Nat.find_spec hbig
    cases hkn : k with
    | zero =>
      apply Set.mem_iUnion.mpr
      refine ⟨0,?_⟩
      change ‖y‖ ≤ R
      simpa only [hkn,pow_zero,one_mul] using hk
    | succ m =>
      apply Set.mem_iUnion.mpr
      refine ⟨m+1,?_,?_⟩
      · apply lt_of_not_ge
        exact Nat.find_min hbig (show m < Nat.find hbig from by change m < k; rw [hkn]; omega)
      · simpa only [hkn] using hk

end Yau.LeafProofs.L05Aux
