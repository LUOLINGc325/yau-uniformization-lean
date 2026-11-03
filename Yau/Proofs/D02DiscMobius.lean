import Yau.Proofs.D02BaseSubsequence

/-! Actual unit-disc automorphisms, defined on the same complex plane as
the original discs, preserve the closed boundary and are smooth there. -/

open scoped Topology ContDiff ComplexConjugate
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

def discMobius (a z : ℂ) : ℂ := (a + z) / (1 + conj a * z)

theorem discMobius_zero (a : ℂ) : discMobius a 0 = a := by simp [discMobius]

theorem discMobius_denom_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 + conj a * z ≠ 0 := by
  have hn : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg a)).trans_lt (by simpa only [mul_one] using ha)
  intro he
  have hneg : conj a * z = -1 := by linear_combination he
  rw [hneg, norm_neg, norm_one] at hn
  exact (lt_irrefl 1) hn

theorem discMobius_normSq_identity (a z : ℂ) :
    Complex.normSq (1 + conj a * z) - Complex.normSq (a + z) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

theorem discMobius_norm_le_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖discMobius a z‖ ≤ 1 := by
  have haSq : Complex.normSq a < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hzSq : Complex.normSq z ≤ 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hd : 0 < Complex.normSq (1 + conj a * z) :=
    Complex.normSq_pos.mpr (discMobius_denom_ne_zero ha hz)
  have hnum : Complex.normSq (a + z) ≤ Complex.normSq (1 + conj a * z) := by
    nlinarith [discMobius_normSq_identity a z,
      mul_nonneg (sub_nonneg.mpr haSq.le) (sub_nonneg.mpr hzSq)]
  have hsq : Complex.normSq (discMobius a z) ≤ 1 := by
    rw [discMobius, Complex.normSq_div]
    exact (div_le_iff₀ hd).mpr (by simpa only [one_mul] using hnum)
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (discMobius a z)]

theorem discMobius_norm_lt_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    ‖discMobius a z‖ < 1 := by
  have haSq : Complex.normSq a < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hzSq : Complex.normSq z < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hd : 0 < Complex.normSq (1 + conj a * z) :=
    Complex.normSq_pos.mpr (discMobius_denom_ne_zero ha hz.le)
  have hnum : Complex.normSq (a + z) < Complex.normSq (1 + conj a * z) := by
    nlinarith [discMobius_normSq_identity a z, mul_pos (sub_pos.mpr haSq) (sub_pos.mpr hzSq)]
  have hsq : Complex.normSq (discMobius a z) < 1 := by
    rw [discMobius, Complex.normSq_div]
    exact (div_lt_iff₀ hd).mpr (by simpa only [one_mul] using hnum)
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (discMobius a z)]

theorem discMobius_norm_eq_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖discMobius a z‖ = 1 := by
  have hd : Complex.normSq (1 + conj a * z) ≠ 0 :=
    (Complex.normSq_pos.mpr (discMobius_denom_ne_zero ha hz.le)).ne'
  have hzSq : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hnum : Complex.normSq (a + z) = Complex.normSq (1 + conj a * z) := by
    have hi := discMobius_normSq_identity a z
    rw [hzSq, sub_self, mul_zero] at hi
    linarith
  have hsq : Complex.normSq (discMobius a z) = 1 := by
    rw [discMobius, Complex.normSq_div, hnum, div_self hd]
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (discMobius a z)]

theorem discMobius_contDiffOn {a : ℂ} (ha : ‖a‖ < 1) :
    ContDiffOn ℂ ∞ (discMobius a) (closedBall (0 : ℂ) 1) := by
  apply (contDiffOn_const.add contDiffOn_id).div
    (contDiffOn_const.add (contDiffOn_const.mul contDiffOn_id))
  intro z hz
  exact discMobius_denom_ne_zero ha (by simpa only [mem_closedBall, dist_zero_right] using hz)

theorem holomorphicDisc_comp_discMobius {n : ℕ} {M : ComplexManifold n}
    {f : ℂ → M.Carrier} (hf : IsHolomorphicDisc f) {a : ℂ} (ha : ‖a‖ < 1) :
    IsHolomorphicDisc (f ∘ discMobius a) := by
  exact hf.comp (discMobius_contDiffOn ha).contMDiffOn (fun z hz => by
    simp only [Set.mem_preimage, mem_closedBall, dist_zero_right] at hz ⊢
    exact discMobius_norm_le_one ha hz)

end Yau.NodeProofs.D02Aux
