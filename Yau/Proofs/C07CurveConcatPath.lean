import Yau.Geometry.Basic

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07CurveConcatAux

open Yau Set Filter

variable {n : ℕ} {M : ComplexManifold n} {x y z : M.Carrier}

def concatPath (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z) (t : ℝ) : M.Carrier :=
  if t ≤ 1 / 2 then γ (2 * t) else η (2 * t - 1)

def concatBreakpoints (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z) : Finset ℝ :=
  insert (1 / 2) ((γ.breakpoints.image (fun t => t / 2)) ∪
    (η.breakpoints.image (fun t => (t + 1) / 2)))

theorem concat_half_ne (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : t ∉ concatBreakpoints γ η) : t ≠ 1 / 2 := by
  intro h
  apply ht
  simp only [concatBreakpoints, Finset.mem_insert]
  exact Or.inl h

theorem concat_left_not_break (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : t ∉ concatBreakpoints γ η) : 2 * t ∉ γ.breakpoints := by
  intro h
  apply ht
  simp only [concatBreakpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inl ⟨2 * t, h, by ring⟩)

theorem concat_right_not_break (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : t ∉ concatBreakpoints γ η) : 2 * t - 1 ∉ η.breakpoints := by
  intro h
  apply ht
  simp only [concatBreakpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr ⟨2 * t - 1, h, by ring⟩)

theorem concat_breakpoints_mem (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : t ∈ concatBreakpoints γ η) : t ∈ Icc (0 : ℝ) 1 := by
  simp only [concatBreakpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at ht
  rcases ht with rfl | hγ | hη
  · norm_num
  · rcases hγ with ⟨s, hs, rfl⟩
    have h := γ.breakpoints_mem s hs
    constructor <;> linarith [h.1, h.2]
  · rcases hη with ⟨s, hs, rfl⟩
    have h := η.breakpoints_mem s hs
    constructor <;> linarith [h.1, h.2]

theorem concatPath_left (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : t ≤ 1 / 2) : concatPath γ η t = γ (2 * t) := if_pos ht

theorem concatPath_right (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : 1 / 2 ≤ t) : concatPath γ η t = η (2 * t - 1) := by
  by_cases h : t ≤ 1 / 2
  · have heq : t = 1 / 2 := le_antisymm h ht
    subst t
    norm_num [concatPath, γ.finish_eq, η.start_eq]
  · exact if_neg h

theorem concatPath_continuousOn (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z) :
    ContinuousOn (concatPath γ η) (Icc (0 : ℝ) 1) := by
  have hL : ContinuousOn (concatPath γ η) (Icc (0 : ℝ) (1 / 2)) := by
    apply (γ.continuous_on.comp (continuous_const.mul continuous_id).continuousOn
      (fun t ht => show 2 * t ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)).congr
    intro t ht
    exact concatPath_left γ η ht.2
  have hR : ContinuousOn (concatPath γ η) (Icc (1 / 2 : ℝ) 1) := by
    apply (η.continuous_on.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
      (fun t ht => show 2 * t - 1 ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ht.1], by linarith [ht.2]⟩)).congr
    intro t ht
    exact concatPath_right γ η ht.1
  apply (hL.union_of_isClosed hR isClosed_Icc isClosed_Icc).mono
  intro t ht
  by_cases h : t ≤ 1 / 2
  · exact Or.inl ⟨ht.1, h⟩
  · exact Or.inr ⟨le_of_not_ge h, ht.2⟩

theorem concatPath_piecewise_c1 (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z)
    {t : ℝ} (ht : t ∉ concatBreakpoints γ η) :
    ContDiffAt ℝ 1 (fun s : ℝ => chartPt (concatPath γ η t) (concatPath γ η s)) t := by
  by_cases h : t < 1 / 2
  · rw [concatPath_left γ η h.le]
    have hAff : ContDiffAt ℝ 1 (fun s : ℝ => 2 * s) t := contDiffAt_const.mul contDiffAt_id
    have hd := (γ.piecewise_c1 (2 * t) (concat_left_not_break γ η ht)).comp t hAff
    apply hd.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with s hs
    exact congrArg (chartPt (γ (2 * t))) (concatPath_left γ η hs.le)
  · have hgt : 1 / 2 < t :=
      lt_of_le_of_ne (le_of_not_gt h) (concat_half_ne γ η ht).symm
    rw [concatPath_right γ η hgt.le]
    have hAff : ContDiffAt ℝ 1 (fun s : ℝ => 2 * s - 1) t :=
      (contDiffAt_const.mul contDiffAt_id).sub contDiffAt_const
    have hd := (η.piecewise_c1 (2 * t - 1) (concat_right_not_break γ η ht)).comp t hAff
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with s hs
    exact congrArg (chartPt (η (2 * t - 1))) (concatPath_right γ η hs.le)

def concatPiecewise (γ : PiecewiseC1Curve x y) (η : PiecewiseC1Curve y z) :
    PiecewiseC1Curve x z where
  toFun := concatPath γ η
  start_eq := by simpa [concatPath] using γ.start_eq
  finish_eq := by
    change concatPath γ η 1 = z
    rw [concatPath_right γ η (by norm_num)]
    convert η.finish_eq using 1 <;> norm_num
  breakpoints := concatBreakpoints γ η
  breakpoints_mem := fun t ht => concat_breakpoints_mem γ η ht
  continuous_on := concatPath_continuousOn γ η
  piecewise_c1 := fun _ ht => concatPath_piecewise_c1 γ η ht

end Yau.Proofs.C07CurveConcatAux
