import Yau.Proofs.F01FieldHeatMaximum
import Yau.Proofs.F01FieldHeatPenalty
import Yau.Proofs.F01SpaceTimeContinuity
import Yau.Proofs.F01ProperPenaltyMaximum
import Yau.Proofs.F01PenaltyLimit

/-! A bounded subcaloric scalar with nonpositive initial values stays
nonpositive. Attainment uses an actual proper smooth function with bounded
native Laplacian, and both vanishing penalties are computed explicitly. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem bounded_subcaloric_nonpos
    (h : ℝ → HermitianField M) (F : M.Carrier → ℝ → ℝ) {T : ℝ} (hT : 0 < T)
    (hF : SmoothSpaceTime F (Icc 0 T)) (hF0 : ∀ x, F x 0 ≤ 0)
    {C : ℝ} (hbound : ∀ x t, t ∈ Icc 0 T → F x t ≤ C)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hf0 : ∀ x, 0 ≤ f x)
    (hproper : ∀ b : ℝ, IsCompact {x | f x ≤ b}) {B : ℝ}
    (hlap : ∀ x t, t ∈ Icc 0 T → laplacian (h t) f x ≤ B)
    (hheat : ∀ x t, t ∈ Ioc 0 T → fieldHeatWithin h (Icc 0 T) (fun s y => F y s) x t ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → F x t ≤ 0 := by
  let κ := (|B| + 1)⁻¹
  have hden : 0 < |B| + 1 := by positivity
  have hκ : 0 < κ := inv_pos.mpr hden
  have hκB : κ * B < 1 := by
    have hratio : |B| / (|B| + 1) < 1 := (div_lt_one hden).mpr (lt_add_one _)
    have hh := mul_le_mul_of_nonneg_left (le_abs_self B) hκ.le
    exact hh.trans_lt (by simpa only [κ, div_eq_mul_inv, mul_comm] using hratio)
  intro x t ht
  apply le_of_all_small_positive_penalties (f := κ * f x + t)
  intro δ hδ hδone
  let V : M.Carrier → ℝ → ℝ := fun y s => F y s - (δ * κ) * f y - δ * s
  have hV : SmoothSpaceTime V (Icc 0 T) := smoothSpaceTime_space_time_penalty hF hf (δ * κ) δ
  have hpen : V x t ≤ 0 := by
    by_contra hnot
    have hpos : 0 < V x t := lt_of_not_ge hnot
    have hupper : ∀ p : M.Carrier × ℝ, p.2 ∈ Icc 0 T →
        V p.1 p.2 ≤ C - (δ * κ) * f p.1 := by
      intro p hp
      have hFbound := hbound p.1 p.2 hp
      have htime := mul_nonneg hδ.le hp.1
      change F p.1 p.2 - (δ * κ) * f p.1 - δ * p.2 ≤ _
      linarith
    obtain ⟨⟨y, s⟩, hs, hmax⟩ := exists_spaceTime_max_of_proper_penalty f hproper (Icc 0 T)
      isCompact_Icc (fun p => V p.1 p.2) (smoothSpaceTime_continuousOn hV)
      (mul_pos hδ hκ) hupper x 0 ⟨le_refl 0, hT.le⟩
    have hposMax : 0 < V y s := hpos.trans_le
      (hmax (show (x, t) ∈ univ ×ˢ Icc 0 T from ⟨mem_univ _, ht⟩))
    have hspos : 0 < s := by
      by_contra hsn
      have hs0 : s = 0 := le_antisymm (le_of_not_gt hsn) hs.1
      rw [hs0] at hposMax
      have hinit := hF0 y
      have hnonneg := mul_nonneg (mul_nonneg hδ.le hκ.le) (hf0 y)
      change 0 < F y 0 - (δ * κ) * f y - δ * 0 at hposMax
      nlinarith
    have hnonneg := fieldHeatWithin_nonneg_at_max h V hV hspos hs.2 hmax
    have hUnique : UniqueDiffWithinAt ℝ (Icc 0 T) s := (uniqueDiffOn_Icc hT) s hs
    rw [fieldHeatWithin_sub_space_time_penalty h hF hf (δ * κ) δ y hs hUnique] at hnonneg
    have hsub := hheat y s ⟨hspos, hs.2⟩
    have hspace := mul_le_mul_of_nonneg_left (hlap y s hs) (mul_nonneg hδ.le hκ.le)
    have hstrict := mul_lt_mul_of_pos_left hκB hδ
    nlinarith
  change F x t - 0 - δ * (κ * f x + t) ≤ 0
  change F x t - (δ * κ) * f x - δ * t ≤ 0 at hpen
  nlinarith

end Yau.NodeProofs.F01Aux
