import Yau.LeafProofs.L16NormalHeatProfile

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Clamp the actual boundary trace to its time slab. Its zero initial value
    makes this the genuine zero-past extension. -/
def tracePastExtension {n : ℕ} (T : ℝ) (B : Point n → ℝ) : Point n → ℝ :=
  fun p => B (p.1,max 0 (min p.2 T))

theorem tracePastExtension_holder {n : ℕ} {α T F : ℝ} (hα : 0 ≤ α)
    (hT : 0 ≤ T) {B : Point n → ℝ}
    (hB : HolderBound α (cylinder Set.univ 0 T) B F) :
    HolderBound α Set.univ (tracePastExtension T B) F :=
  holderBound_timeClamp hα hT hB

theorem tracePastExtension_eqOn {n : ℕ} (T : ℝ) (B : Point n → ℝ) :
    Set.EqOn (tracePastExtension T B) B (cylinder Set.univ 0 T) :=
  timeClamp_eqOn T B

theorem tracePastExtension_zero_past {n : ℕ} {T : ℝ} {B : Point n → ℝ}
    (hB0 : ∀ x, B (x,0) = 0) {p : Point n} (hp : p.2 ≤ 0) :
    tracePastExtension T B p = 0 := by
  have hClamp : max 0 (min p.2 T) = 0 := max_eq_left ((min_le_left _ _).trans hp)
  simp only [tracePastExtension,hClamp,hB0]

theorem tracePastExtension_normal_invariant {n : ℕ} {e : Space n} {T : ℝ}
    (hT : 0 ≤ T) {B : Point n → ℝ}
    (hInv : ∀ (x : Space n) (s t : ℝ), t ∈ Set.Icc 0 T → B (x+s • e,t) = B (x,t)) :
    ∀ (x : Space n) (s t : ℝ), tracePastExtension T B (x+s • e,t) = tracePastExtension T B (x,t) := by
  intro x s t
  exact hInv x s _ ⟨le_max_left _ _,max_le hT (min_le_right _ _)⟩

theorem halfSpaceBoundaryProjection_normal_shift {n : ℕ} {e : Space n}
    (he : ‖e‖ = 1) (x : Space n) (s : ℝ) :
    halfSpaceBoundaryProjection e (x+s • e) = halfSpaceBoundaryProjection e x := by
  rw [map_add,map_smul,halfSpaceBoundaryProjection_apply he e]
  simp only [real_inner_self_eq_norm_sq,he,one_pow,one_smul,sub_self,smul_zero,add_zero]

theorem boundary_trace_initial_zero {n : ℕ} {e : Space n} {f : Point n → ℝ}
    (hCompat : ∀ x : Space n, inner ℝ e x = 0 → f (x,0) = 0) :
    ∀ x, f (halfSpaceBoundaryProjection e x,0) = 0 := by
  intro x
  exact hCompat _ (halfSpaceBoundaryProjection_normal _ _)

theorem boundary_trace_normal_invariant {n : ℕ} {e : Space n} (he : ‖e‖ = 1)
    (f : Point n → ℝ) : ∀ (x : Space n) (s t : ℝ),
      f (halfSpaceBoundaryProjection e (x+s • e),t) = f (halfSpaceBoundaryProjection e x,t) := by
  intro x s t
  rw [halfSpaceBoundaryProjection_normal_shift he]

theorem tracePastExtension_small_time_bound {n : ℕ} {α T F : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) {B : Point n → ℝ}
    (hB : HolderBound α (cylinder Set.univ 0 T) B F) (hB0 : ∀ x, B (x,0) = 0)
    {t s : ℝ} (ht : t ∈ Set.Icc 0 T) (hs : s ≤ t) (x : Space n) :
    |tracePastExtension T B (x,s)| ≤ F*t^(α/2) := by
  by_cases hs0 : s ≤ 0
  · rw [tracePastExtension_zero_past hB0 hs0]
    simpa only [abs_zero] using mul_nonneg hB.1 (Real.rpow_nonneg ht.1 (α/2))
  · have hsPos : 0 < s := lt_of_not_ge hs0
    have hsT : s ≤ T := hs.trans ht.2
    have h := hB.2.2 (x,s) ⟨Set.mem_univ _,hsPos.le,hsT⟩ (x,0)
      ⟨Set.mem_univ _,le_rfl,hT⟩
    rw [hB0] at h
    have hExpr : |B (x,s)| ≤ F*s^(α/2) := by
      simpa only [sub_zero,Real.norm_eq_abs,holderWeight,sub_self,norm_zero,
        Real.zero_rpow hα.ne',zero_add,abs_of_pos hsPos] using h
    rw [tracePastExtension_eqOn T B ⟨Set.mem_univ _,hsPos.le,hsT⟩]
    exact hExpr.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hsPos.le hs (by positivity)) hB.1)

end Yau.LeafProofs.L16Aux
