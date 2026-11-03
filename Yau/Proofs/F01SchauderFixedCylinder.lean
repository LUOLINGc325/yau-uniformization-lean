import Yau.Proofs.F01BackwardHolderPatching
import Yau.Proofs.F01SchauderPatchDerivatives

/-! Uniform actual backward-patch estimates give the full original
Schauder bound on one fixed closed inner cylinder. The field and its
chart centers are chosen after the numerical budget. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem schauder_fixed_cylinder_budget {κ β C : ℝ}
    (hκ : 0 < κ) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (S : Set (Space n)) (a b r l s : ℝ) (u : Point n → ℝ),
      l < s → ball 0 r ⊆ S → Icc l s ⊆ Icc a b → C2 (cylinder S a b) u →
      (∀ c ∈ ball 0 r, ∀ τ ∈ Icc l s,
        MapsTo (fun x => κ • x + c) (ball 0 1) S ∧
        MapsTo (fun t => τ + κ ^ 2 * t) (Icc (-1) 0) (Icc a b)) →
      (∀ c ∈ ball 0 r, ∀ τ ∈ Icc l s,
        SchauderBound β (backward 1) (affineParabolicPullback κ c τ u) C) →
      SchauderBound β (cylinder (ball 0 r) l s) u B := by
  have hScale : 0 ≤ |(κ ^ 2)⁻¹| * C := mul_nonneg (abs_nonneg _) hC
  obtain ⟨Bh, hBh, hHess⟩ := backward_holder_patching_budget (n := n)
    (E := Space n →L[ℝ] Space n →L[ℝ] ℝ) hκ hβ hScale
  obtain ⟨Bt, hBt, hTime⟩ := backward_holder_patching_budget (n := n) (E := ℝ) hκ hβ hScale
  let B := 1 + C + C / κ + Bh + Bt
  have hDiv : 0 ≤ C / κ := div_nonneg hC hκ.le
  have hB : 0 < B := by dsimp only [B]; linarith
  have hCB : C ≤ B := by dsimp only [B]; linarith
  have hDB : C / κ ≤ B := by dsimp only [B]; linarith
  have hHB : Bh ≤ B := by dsimp only [B]; linarith
  have hTB : Bt ≤ B := by dsimp only [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro S a b r l s u hls hSpace hClock hu hMaps hPatch
  have hSpaceId : MapsTo (fun x : Space n => (1 : ℝ) • x + 0) (ball 0 r) S := by
    intro x hx
    simpa only [one_smul, add_zero] using hSpace hx
  have hClockId : MapsTo (fun t : ℝ => 0 + (1 : ℝ) ^ 2 * t) (Icc l s) (Icc a b) := by
    intro t ht
    simpa only [one_pow, one_mul, zero_add] using hClock ht
  have hPull : affineParabolicPullback 1 (0 : Space n) 0 u = u := by
    funext p
    simp [affineParabolicPullback, affineParabolicPoint]
  have hPoint (p : Point n) : affineParabolicPoint 1 (0 : Space n) 0 p = p := by
    simp [affineParabolicPoint]
  have hC2 : C2 (cylinder (ball 0 r) l s) u := by
    have hh := c2_affineParabolicPullback hls hu hSpaceId hClockId
    rw [hPull] at hh
    exact hh
  have hEqTime (p : Point n) (hp : p ∈ cylinder (ball 0 r) l s) :
      timeD (cylinder (ball 0 r) l s) u p = timeD (cylinder S a b) u p := by
    have hh := timeD_affineParabolicPullback hls hu hSpaceId hClockId hp
    rw [hPull, hPoint] at hh
    simpa only [one_pow, one_mul] using hh
  have hH : HolderBound β (cylinder (ball 0 r) l s) (spatialDD u) Bh := by
    apply hHess r l s (spatialDD u)
    intro c hc τ hτ
    exact affine_schauder_patch_hessian_holder hκ.ne' (hPatch c hc τ hτ)
  have hT : HolderBound β (cylinder (ball 0 r) l s) (timeD (cylinder S a b) u) Bt := by
    apply hTime r l s (timeD (cylinder S a b) u)
    intro c hc τ hτ
    exact affine_schauder_patch_time_holder hκ.ne' hu
      (hMaps c hc τ hτ).1 (hMaps c hc τ hτ).2 (hPatch c hc τ hτ)
  refine ⟨hC2, hB.le, ?_, holderBound_mono_const hH hHB, ?_⟩
  · intro p hp
    have h0 : ((0 : Space n), (0 : ℝ)) ∈ backward 1 := by
      constructor <;> norm_num [backward, mem_ball, dist_zero_right]
    have hsup := (hPatch p.1 hp.1 p.2 hp.2).2.2.1 _ h0
    have huSup : |u p| ≤ C := by
      simpa only [affineParabolicPullback, affineParabolicPoint, smul_zero,
        zero_add, mul_zero, add_zero] using hsup.1
    have hD : κ * ‖spatialD u p‖ ≤ C := by
      have hd := hsup.2
      rw [spatialD_affineParabolicPullback, norm_smul, Real.norm_eq_abs, abs_of_pos hκ] at hd
      simpa only [affineParabolicPoint, smul_zero, zero_add, mul_zero, add_zero] using hd
    exact ⟨huSup.trans hCB, ((le_div_iff₀ hκ).mpr (by nlinarith)).trans hDB⟩
  · apply holderBound_congr_on_native (holderBound_mono_const hT hTB)
    intro p hp
    exact (hEqTime p hp).symm

end Yau.NodeProofs.F01Aux
