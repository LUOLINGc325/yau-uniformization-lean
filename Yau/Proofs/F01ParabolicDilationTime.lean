import Yau.Proofs.F01ParabolicDilation

/-! The actual closed-face time derivative of the normalized zero
extension is the original scalar time jet at the dilated clamped point. -/
noncomputable section
open Set Metric
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem zero_extended_parabolicRescalePotential_timeD
    {F D : Point n → ℝ} {ρ r T : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hF0 : ∀ x ∈ ball 0 r, F (x, 0) = 0)
    (hD0 : ∀ x ∈ ball 0 r, D (x, 0) = 0)
    (hJet : ∀ x ∈ ball 0 r, ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun t => F (x, t)) (D (x, s)) (Icc 0 T) s)
    {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
    timeD (ball 0 1 ×ˢ Icc (-1) 1)
      (forwardZeroSpaceTime (parabolicRescalePotential ρ F)) p =
      D (parabolicDilation ρ (p.1, max p.2 0)) := by
  have hm : MapsTo (parabolicDilation (n := n) ρ)
      (ball 0 1 ×ˢ Icc 0 1) (ball 0 r ×ˢ Icc 0 T) :=
    parabolicDilation_maps_positive hρ hρr hρT
  have hzero : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hxρ : ρ • p.1 ∈ ball (0 : Space n) r := spatialDilation_mem_ball hρ hρr hp.1
  have hv0 : parabolicRescalePotential ρ F (p.1, 0) = 0 := by
    change (ρ ^ 2)⁻¹ * F (ρ • p.1, ρ ^ 2 * 0) = 0
    rw [mul_zero, hF0 _ hxρ, mul_zero]
  have hd0 : D (parabolicDilation ρ (p.1, 0)) = 0 := by
    simpa only [parabolicDilation, mul_zero] using hD0 _ hxρ
  have hj : HasDerivWithinAt
      (forwardZeroExtension (fun t => parabolicRescalePotential ρ F (p.1, t)))
      (forwardZeroExtension (fun t => D (parabolicDilation ρ (p.1, t))) p.2)
      (Icc (-1) 1) p.2 :=
    forwardZeroExtension_time_jet zero_lt_one hv0 hd0
      (fun s hs => parabolicRescalePotential_time_jet hρ hρr hρT hJet
        (p := (p.1, s)) ⟨hp.1, hs⟩) hp.2
  have hset : {s : ℝ | (p.1, s) ∈ ball 0 1 ×ˢ Icc (-1) 1} = Icc (-1) 1 := by
    ext s
    exact and_iff_right hp.1
  unfold timeD
  rw [hset]
  change derivWithin (forwardZeroExtension (fun t => parabolicRescalePotential ρ F (p.1, t)))
    (Icc (-1) 1) p.2 = _
  rw [hj.derivWithin ((uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)) p.2 hp.2)]
  exact forwardZeroSpaceTime_eq_clamped
    (F := fun q : Point n => D (parabolicDilation ρ q))
    (S := {p.1}) (fun x hx => by simpa only [mem_singleton_iff.mp hx] using hd0)
    (mem_singleton p.1) p.2

end Yau.NodeProofs.F01Aux
