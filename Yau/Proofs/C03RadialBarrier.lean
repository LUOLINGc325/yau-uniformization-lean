import Yau.Proofs.C03PshGluing

/-! The actual radial barrier is globally smooth and plurisubharmonic.
Its separation on a smaller ball leaves the seed and pole germs unchanged. -/

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs.L22Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def radialBarrier (R M L : ℝ) (z : ComplexVector n) : ℝ :=
  M + 2 + L * (‖z‖ ^ 2 - R ^ 2)

theorem radialBarrier_contDiff (R M L : ℝ) :
    ContDiff ℝ ∞ (radialBarrier (n := n) R M L) :=
  contDiff_const.add (contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const))

theorem complexLeviQuadratic_norm_sq (z v : ComplexVector n) :
    complexLeviQuadratic (fun w : ComplexVector n => ‖w‖ ^ 2) z v = ‖v‖ ^ 2 := by
  have HD : fderiv ℝ (fderiv ℝ (fun w : ComplexVector n => ‖w‖ ^ 2)) z =
      2 • innerSL ℝ (E := ComplexVector n) := by
    rw [fderiv_norm_sq]
    exact (2 • innerSL ℝ (E := ComplexVector n)).fderiv
  have hself : (innerSL ℝ (E := ComplexVector n)) v v = ‖v‖ ^ 2 := by
    change inner ℝ v v = ‖v‖ ^ 2
    exact real_inner_self_eq_norm_sq v
  have hI : (innerSL ℝ (E := ComplexVector n)) (Complex.I • v) (Complex.I • v) = ‖v‖ ^ 2 := by
    change inner ℝ (Complex.I • v) (Complex.I • v) = ‖v‖ ^ 2
    rw [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  simp only [complexLeviQuadratic, HD, two_smul, add_apply]
  rw [hself, hI]
  ring

theorem radialBarrier_complexLeviQuadratic (R M L : ℝ) (z v : ComplexVector n) :
    complexLeviQuadratic (radialBarrier R M L) z v = L * ‖v‖ ^ 2 := by
  have heq : radialBarrier (n := n) R M L =
      fun w : ComplexVector n => (M + 2 - L * R ^ 2) + L * ‖w‖ ^ 2 := by
    funext w
    dsimp only [radialBarrier]
    ring
  rw [heq, complexLeviQuadratic_add contDiffAt_const
    (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
    complexLeviQuadratic_const_mul (contDiff_norm_sq ℝ).contDiffAt L v,
    complexLeviQuadratic_norm_sq]
  have hc : complexLeviQuadratic (fun _ : ComplexVector n => M + 2 - L * R ^ 2) z v = 0 := by
    simp [complexLeviQuadratic]
  rw [hc, zero_add]

theorem radialBarrier_leviC_posSemidef (R M L : ℝ) (hL : 0 ≤ L) (z : ComplexVector n) :
    (leviC (radialBarrier (n := n) R M L) z).PosSemidef := by
  apply (leviC_posSemidef_iff ((radialBarrier_contDiff R M L).contDiffAt.of_le (by simp))).mpr
  intro v
  rw [radialBarrier_complexLeviQuadratic]
  exact mul_nonneg hL (sq_nonneg _)

theorem radialBarrier_boundary (R M L : ℝ) (z : ComplexVector n) (hz : ‖z‖ = R) :
    radialBarrier R M L z = M + 2 := by
  simp only [radialBarrier, hz, sub_self, mul_zero, add_zero]

theorem radialBarrier_le (R M L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (z : ComplexVector n) (hz : ‖z‖ ≤ R) : radialBarrier R M L z ≤ M + 2 := by
  have hs : ‖z‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg z) hR).2 hz
  have H := mul_nonpos_of_nonneg_of_nonpos hL (sub_nonpos.mpr hs)
  dsimp only [radialBarrier]
  linarith

theorem exists_radialBarrier_separation (R s M : ℝ) (hs : 0 ≤ s) (hsR : s < R)
    (hM : 0 ≤ M) : ∃ L : ℝ, 0 < L ∧ ∀ z : ComplexVector n,
      ‖z‖ ≤ s → radialBarrier R M L z ≤ -2 := by
  have hR : 0 < R := lt_of_le_of_lt hs hsR
  have hden : 0 < R ^ 2 - s ^ 2 := by nlinarith
  let L := (M + 4) / (R ^ 2 - s ^ 2)
  have hL : 0 < L := div_pos (by linarith) hden
  refine ⟨L, hL, ?_⟩
  intro z hz
  have hzs : ‖z‖ ^ 2 ≤ s ^ 2 := (sq_le_sq₀ (norm_nonneg z) hs).2 hz
  have H := mul_le_mul_of_nonneg_left (sub_le_sub_right hzs (R ^ 2)) hL.le
  have hcancel : L * (R ^ 2 - s ^ 2) = M + 4 := by
    dsimp only [L]
    exact div_mul_cancel₀ _ hden.ne'
  dsimp only [radialBarrier]
  nlinarith

end Yau.Proofs.C03Aux
