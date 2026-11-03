import Yau.Proofs.F01HolderBilinear

/-! Backward clock patches with varying terminal center control an
entire short interval, including an open terminal interval. There is
no time-extension or future-buffer hypothesis. -/
noncomputable section
open Set
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

theorem holder_from_common_backward_clock_patches
    (O : Set (Space n)) (I : Set ℝ) (f : Point n → F)
    {κ R β C : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hMax : ∀ s ∈ I, ∀ t ∈ I, max s t ∈ I)
    (hDiam : ∀ s ∈ I, ∀ t ∈ I, |s - t| ≤ κ * R)
    (hLocal : ∀ τ ∈ I, HolderBound β (O ×ˢ Icc (-R) 0)
      (fun p => f (p.1, τ + κ * p.2)) C) :
    HolderBound β (O ×ˢ I) f ((1 + κ⁻¹ ^ (β / 2)) * C) := by
  let H : ℝ := κ⁻¹ ^ (β / 2)
  have hH : 0 ≤ H := Real.rpow_nonneg (inv_nonneg.mpr hκ.le) _
  have hBC : C ≤ (1 + H) * C := by nlinarith
  refine ⟨mul_nonneg (by positivity) hC, ?_, ?_⟩
  · intro p hp
    have h0 : (p.1, (0 : ℝ)) ∈ O ×ˢ Icc (-R) 0 := ⟨hp.1, by linarith, le_rfl⟩
    have hh := (hLocal p.2 hp.2).2.1 _ h0
    simpa only [mul_zero, add_zero] using hh.trans hBC
  · intro p hp q hq
    let τ := max p.2 q.2
    have hτ : τ ∈ I := hMax p.2 hp.2 q.2 hq.2
    have hClock (s : ℝ) (hs : s ∈ I) (hsτ : s ≤ τ) : (s - τ) / κ ∈ Icc (-R) 0 := by
      constructor
      · apply (le_div_iff₀ hκ).mpr
        have hh := (abs_le.mp (hDiam s hs τ hτ)).1
        nlinarith
      · exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsτ) hκ.le
    let p' : Point n := (p.1, (p.2 - τ) / κ)
    let q' : Point n := (q.1, (q.2 - τ) / κ)
    have hp' : p' ∈ O ×ˢ Icc (-R) 0 := ⟨hp.1, hClock p.2 hp.2 (le_max_left _ _)⟩
    have hq' : q' ∈ O ×ˢ Icc (-R) 0 := ⟨hq.1, hClock q.2 hq.2 (le_max_right _ _)⟩
    have hRestore (s : ℝ) : τ + κ * ((s - τ) / κ) = s := by field_simp; ring
    have hWeight : holderWeight β p' q' =
        ‖p.1 - q.1‖ ^ β + H * |p.2 - q.2| ^ (β / 2) := by
      have he : (p.2 - τ) / κ - (q.2 - τ) / κ = κ⁻¹ * (p.2 - q.2) := by ring
      dsimp only [holderWeight, p', q']
      rw [he, abs_mul, abs_of_pos (inv_pos.mpr hκ),
        Real.mul_rpow (inv_nonneg.mpr hκ.le) (abs_nonneg _)]
    have hh := (hLocal τ hτ).2.2 p' hp' q' hq'
    change ‖f (p.1, τ + κ * ((p.2 - τ) / κ)) -
      f (q.1, τ + κ * ((q.2 - τ) / κ))‖ ≤ _ at hh
    rw [hRestore, hRestore, hWeight] at hh
    change ‖f p - f q‖ ≤ ((1 + H) * C) * holderWeight β p q
    refine hh.trans ?_
    unfold holderWeight
    have hs : 0 ≤ ‖p.1 - q.1‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    have ht : 0 ≤ |p.2 - q.2| ^ (β / 2) := Real.rpow_nonneg (abs_nonneg _) _
    nlinarith [mul_nonneg hC hs, mul_nonneg hC ht, mul_nonneg hH hs,
      mul_nonneg (mul_nonneg hH hC) hs]

end Yau.NodeProofs.F01Aux
