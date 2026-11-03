import Yau.Proofs.F01SpatialDilationLevi
import Yau.Proofs.F01ZeroExtensionParabolicC2

/-! Actual simultaneous spatial and temporal dilation of the original
potential, with its closed-slab first time jet and parabolic C2 zero extension. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def parabolicDilation (ρ : ℝ) (p : Point n) : Point n := (ρ • p.1, ρ ^ 2 * p.2)

def parabolicRescalePotential (ρ : ℝ) (F : Point n → ℝ) (p : Point n) : ℝ :=
  (ρ ^ 2)⁻¹ * F (parabolicDilation ρ p)

theorem parabolicDilation_contDiff (ρ : ℝ) : ContDiff ℝ ∞ (parabolicDilation (n := n) ρ) := by
  change ContDiff ℝ ∞ (fun p : Point n => (ρ • p.1, ρ ^ 2 * p.2))
  fun_prop

theorem spatialDilation_mem_ball {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    {x : Space n} (hx : x ∈ ball 0 1) : ρ • x ∈ ball 0 r := by
  have hx1 : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] using
    (mul_lt_mul_of_pos_left hx1 hρ).trans_le (by simpa using hρr)

theorem parabolicDilation_maps_positive {ρ r T : ℝ} (hρ : 0 < ρ)
    (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T) :
    MapsTo (parabolicDilation (n := n) ρ)
      (ball 0 1 ×ˢ Icc 0 1) (ball 0 r ×ˢ Icc 0 T) := by
  intro p hp
  have hx : ‖p.1‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hp.1
  refine ⟨?_, mul_nonneg (sq_nonneg _) hp.2.1, ?_⟩
  · simpa only [parabolicDilation, mem_ball, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hρ] using
      (mul_lt_mul_of_pos_left hx hρ).trans_le (by simpa using hρr)
  · exact (mul_le_of_le_one_right (sq_nonneg ρ) hp.2.2).trans hρT

theorem parabolicRescalePotential_smooth {F : Point n → ℝ} {ρ r T : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hF : ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T)) :
    ContDiffOn ℝ ∞ (parabolicRescalePotential ρ F) (ball 0 1 ×ˢ Icc 0 1) :=
  contDiffOn_const.mul (hF.comp (parabolicDilation_contDiff ρ).contDiffOn
    (parabolicDilation_maps_positive hρ hρr hρT))

theorem parabolicRescalePotential_time_jet {F D : Point n → ℝ} {ρ r T : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hF : ∀ x ∈ ball 0 r, ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun t => F (x, t)) (D (x, s)) (Icc 0 T) s)
    {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc 0 1) :
    HasDerivWithinAt (fun t => parabolicRescalePotential ρ F (p.1, t))
      (D (parabolicDilation ρ p)) (Icc 0 1) p.2 := by
  have hm := parabolicDilation_maps_positive hρ hρr hρT hp
  have htmap : MapsTo (fun t : ℝ => ρ ^ 2 * t) (Icc 0 1) (Icc 0 T) := by
    intro t ht
    exact ⟨mul_nonneg (sq_nonneg _) ht.1,
      (mul_le_of_le_one_right (sq_nonneg ρ) ht.2).trans hρT⟩
  have ht : HasDerivWithinAt (fun t : ℝ => ρ ^ 2 * t) (ρ ^ 2) (Icc 0 1) p.2 := by
    convert ((hasDerivAt_id p.2).const_mul (ρ ^ 2)).hasDerivWithinAt using 1 <;> simp
  have hc := ((hF _ hm.1 _ hm.2).comp p.2 ht htmap).const_mul ((ρ ^ 2)⁻¹)
  convert hc using 1
  · rfl
  · dsimp only [parabolicDilation]
    field_simp [hρ.ne']

theorem parabolicRescalePotential_zeroExtension_C2 {F D : Point n → ℝ} {ρ r T : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hF : ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T))
    (hF0 : ∀ x ∈ ball 0 r, F (x, 0) = 0)
    (hD0 : ∀ x ∈ ball 0 r, D (x, 0) = 0)
    (hJet : ∀ x ∈ ball 0 r, ∀ s ∈ Icc 0 T,
      HasDerivWithinAt (fun t => F (x, t)) (D (x, s)) (Icc 0 T) s) :
    C2 (ball 0 1 ×ˢ Icc (-1) 1) (forwardZeroSpaceTime (parabolicRescalePotential ρ F)) := by
  have hm : MapsTo (parabolicDilation (n := n) ρ)
      (ball 0 1 ×ˢ Icc 0 1) (ball 0 r ×ˢ Icc 0 T) :=
    parabolicDilation_maps_positive hρ hρr hρT
  have hzero : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have hs : ContDiffOn ℝ ∞ (parabolicRescalePotential ρ F) (ball 0 1 ×ˢ Icc 0 1) :=
    parabolicRescalePotential_smooth hρ hρr hρT hF
  have hinitValue : ∀ x ∈ ball (0 : Space n) 1, parabolicRescalePotential ρ F (x, 0) = 0 := by
    intro x hx
    have hxρ : ρ • x ∈ ball (0 : Space n) r := spatialDilation_mem_ball hρ hρr hx
    change (ρ ^ 2)⁻¹ * F (ρ • x, ρ ^ 2 * 0) = 0
    rw [mul_zero, hF0 _ hxρ, mul_zero]
  have hinitJet : ∀ x ∈ ball (0 : Space n) 1,
      HasDerivWithinAt (fun t => parabolicRescalePotential ρ F (x, t)) 0 (Icc 0 1) 0 := by
    intro x hx
    have hxρ : ρ • x ∈ ball (0 : Space n) r := spatialDilation_mem_ball hρ hρr hx
    have hj : HasDerivWithinAt (fun t => parabolicRescalePotential ρ F (x, t))
        (D (parabolicDilation ρ (x, 0))) (Icc 0 1) 0 :=
      parabolicRescalePotential_time_jet hρ hρr hρT hJet (p := (x, 0)) ⟨hx, hzero⟩
    simpa only [parabolicDilation, mul_zero, hD0 _ hxρ] using hj
  exact forwardZeroSpaceTime_parabolic_C2 isOpen_ball zero_lt_one (by norm_num)
    hs hinitValue hinitJet

end Yau.NodeProofs.F01Aux
