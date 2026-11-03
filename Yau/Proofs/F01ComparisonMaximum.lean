import Yau.Proofs.F01ComparisonTime
import Yau.Proofs.F01BoundedMaximum

/-! The actual explicit comparison function is smooth, bounded below by
the actual potential/logdet bounds, and nonnegative by the native maximum
principle once its genuine heat inequality is supplied. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem comparisonFunction_smoothSpaceTime {U P : M.Carrier → ℝ → ℝ}
    {φ : M.Carrier → ℝ} {I : Set ℝ} (hU : SmoothSpaceTime U I)
    (hP : SmoothSpaceTime P I) (hφ : SmoothFn φ) (D : ℝ) :
    SmoothSpaceTime (comparisonFunction D n U P φ) I := by
  intro a
  exact (((contDiffOn_const.sub contDiffOn_snd).mul (hP a)).add (hU a)).sub
    (contDiffOn_const.mul ((hφ a).comp contDiffOn_fst (fun p hp => hp.1))) |>.add
      (contDiffOn_const.mul contDiffOn_snd)

theorem comparisonFunction_neg_upper_bound {U P : M.Carrier → ℝ → ℝ}
    {φ : M.Carrier → ℝ} {D T CU CP : ℝ} (hD : 0 ≤ D) (hCP : 0 ≤ CP)
    (hU : ∀ x t, t ∈ Icc 0 T → |U x t| ≤ CU)
    (hP : ∀ x t, t ∈ Icc 0 T → |P x t| ≤ CP) (hφ : ∀ x, φ x ≤ 0)
    (x : M.Carrier) {t : ℝ} (ht : t ∈ Icc 0 T) :
    -comparisonFunction D n U P φ x t ≤ (|D| + T) * CP + CU := by
  have hdt : |D - t| ≤ |D| + T := by
    have ha := abs_sub_le D 0 t
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg ht.1] at ha
    linarith [ht.2]
  have hprod : -((D - t) * P x t) ≤ (|D| + T) * CP :=
    (neg_le_abs ((D - t) * P x t)).trans (by
      rw [abs_mul]
      exact mul_le_mul hdt (hP x t ht) (abs_nonneg _) ((abs_nonneg _).trans hdt))
  have hUneg := (neg_le_abs (U x t)).trans (hU x t ht)
  have hφterm := mul_nonpos_of_nonneg_of_nonpos hD (hφ x)
  have hnt : 0 ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht.1
  unfold comparisonFunction
  linarith

theorem comparisonFunction_nonneg
    (h : ℝ → HermitianField M) {U P : M.Carrier → ℝ → ℝ} {φ : M.Carrier → ℝ}
    {D T CU CP : ℝ} (hT : 0 < T) (hD : 0 ≤ D) (hCP : 0 ≤ CP)
    (hU : SmoothSpaceTime U (Icc 0 T)) (hP : SmoothSpaceTime P (Icc 0 T))
    (hφ : SmoothFn φ) (hφsign : ∀ x, φ x ≤ 0)
    (hU0 : ∀ x, U x 0 = 0) (hP0 : ∀ x, P x 0 = 0)
    (hUbound : ∀ x t, t ∈ Icc 0 T → |U x t| ≤ CU)
    (hPbound : ∀ x t, t ∈ Icc 0 T → |P x t| ≤ CP)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hf0 : ∀ x, 0 ≤ f x)
    (hproper : ∀ b : ℝ, IsCompact {x | f x ≤ b}) {B : ℝ}
    (hlap : ∀ x t, t ∈ Icc 0 T → laplacian (h t) f x ≤ B)
    (hheat : ∀ x t, t ∈ Ioc 0 T → 0 ≤
      fieldHeatWithin h (Icc 0 T) (fun s y => comparisonFunction D n U P φ y s) x t) :
    ∀ x t, t ∈ Icc 0 T → 0 ≤ comparisonFunction D n U P φ x t := by
  have hQ := comparisonFunction_smoothSpaceTime hU hP hφ D
  have hnegativeHeat : ∀ y s, s ∈ Ioc 0 T →
      fieldHeatWithin h (Icc 0 T) (fun r z => -comparisonFunction D n U P φ z r) y s ≤ 0 := by
    intro y s hs
    have hd := (smoothSpaceTime_time_slice hQ y s ⟨hs.1.le, hs.2⟩).differentiableWithinAt (by simp)
    have hu : UniqueDiffWithinAt ℝ (Icc 0 T) s := (uniqueDiffOn_Icc hT) s ⟨hs.1.le, hs.2⟩
    have htime := hd.hasDerivWithinAt.neg.derivWithin hu
    change derivWithin (fun r => -comparisonFunction D n U P φ y r) (Icc 0 T) s =
      -derivWithin (comparisonFunction D n U P φ y) (Icc 0 T) s at htime
    have hspace := smoothSpaceTime_slice hQ ⟨hs.1.le, hs.2⟩
    have hnegspace := laplacian_const_mul_native (h s) hspace (-1)
    simp only [neg_one_mul] at hnegspace
    unfold fieldHeatWithin
    rw [htime, hnegspace]
    have hh := hheat y s hs
    unfold fieldHeatWithin at hh
    linarith
  have hnonpos := bounded_subcaloric_nonpos h
    (fun x t => -comparisonFunction D n U P φ x t) hT (fun a => (hQ a).neg)
    (fun x => by rw [comparisonFunction_initial D n U P φ hU0 hP0]; nlinarith [hφsign x])
    (fun x t ht => comparisonFunction_neg_upper_bound hD hCP hUbound hPbound hφsign x ht)
    f hf hf0 hproper hlap hnegativeHeat
  intro x t ht
  exact neg_nonpos.mp (hnonpos x t ht)

end Yau.NodeProofs.F01Aux
