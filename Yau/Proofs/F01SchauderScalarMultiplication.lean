import Yau.Proofs.F01AffineParabolicSchauder

/-! The actual parabolic C2 and Schauder predicates are homogeneous
under real multiplication, including their within-time derivatives.
This restores the precise amplitude in normalized initial estimates. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem holderBound_real_smul_native {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Q : Set (Point n)} {β C : ℝ} {f : Point n → V}
    (hf : HolderBound β Q f C) (κ : ℝ) :
    HolderBound β Q (fun p => κ • f p) (|κ| * C) := by
  refine ⟨mul_nonneg (abs_nonneg _) hf.1, ?_, ?_⟩
  · intro p hp
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf.2.1 p hp) (abs_nonneg _)
  · intro p hp q hq
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hf.2.2 p hp q hq) (abs_nonneg _)).trans_eq (by ring)

theorem spatialD_real_smul (κ : ℝ) (u : Point n → ℝ) (p : Point n) :
    spatialD (fun q => κ * u q) p = κ • spatialD u p := by
  change fderiv ℝ (κ • (fun x => u (x, p.2))) p.1 = _
  rw [fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ), Pi.smul_apply]
  rfl

theorem spatialDD_real_smul (κ : ℝ) (u : Point n → ℝ) (p : Point n) :
    spatialDD (fun q => κ * u q) p = κ • spatialDD u p := by
  have he : (fun x => spatialD (fun q => κ * u q) (x, p.2)) =
      (fun x => κ • spatialD u (x, p.2)) :=
    funext (fun x => spatialD_real_smul κ u (x, p.2))
  change fderiv ℝ (fun x => spatialD (fun q => κ * u q) (x, p.2)) p.1 = _
  rw [he]
  change fderiv ℝ (κ • (fun x => spatialD u (x, p.2))) p.1 = _
  rw [fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ), Pi.smul_apply]
  rfl

theorem timeD_real_mul (κ : ℝ) (Q : Set (Point n)) (u : Point n → ℝ) (p : Point n) :
    timeD Q (fun q => κ * u q) p = κ * timeD Q u p := by
  exact derivWithin_const_mul_field κ

theorem schauderBound_real_mul {Q : Set (Point n)} {β C : ℝ} {u : Point n → ℝ}
    (hu : SchauderBound β Q u C) (κ : ℝ) :
    SchauderBound β Q (fun p => κ * u p) (|κ| * C) := by
  have hDD := holderBound_real_smul_native hu.2.2.2.1 κ
  have hTime := holderBound_real_smul_native hu.2.2.2.2 κ
  refine ⟨Yau.LeafProofs.L16Aux.c2_const_smul hu.1 κ,
    mul_nonneg (abs_nonneg _) hu.2.1, ?_, ?_, ?_⟩
  · intro p hp
    constructor
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hu.2.2.1 p hp).1 (abs_nonneg _)
    · rw [spatialD_real_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hu.2.2.1 p hp).2 (abs_nonneg _)
  · apply holderBound_congr_on_native hDD
    intro p hp
    exact (spatialDD_real_smul κ u p).symm
  · apply holderBound_congr_on_native hTime
    intro p hp
    exact (timeD_real_mul κ Q u p).symm

end Yau.NodeProofs.F01Aux
