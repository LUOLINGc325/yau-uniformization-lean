import Mathlib

/-! The exact exponential cancellation and domination used in the nonlinear
compact-mass proof of F04. -/

open scoped Topology

namespace Yau.F04Proof

theorem nonlinear_exponential_cancellation (w L R : ℝ) :
    Real.exp w * (Real.exp (-w) * L + (1 - Real.exp (-w)) * R) -
      (Real.exp w - 1) * R = L := by
  have he : Real.exp w * Real.exp (-w) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    _ = (Real.exp w * Real.exp (-w)) * L +
        (1 - Real.exp w * Real.exp (-w)) * R := by ring
    _ = L := by rw [he]; ring

theorem nonlinear_mass_hasDerivAt {w ρ : ℝ → ℝ} {L R t : ℝ}
    (hw : HasDerivAt w
      (Real.exp (-w t) * L + (1 - Real.exp (-w t)) * R) t)
    (hρ : HasDerivAt ρ R t) :
    HasDerivAt (fun s => (Real.exp (w s) - 1) * Real.exp (-ρ s))
      (L * Real.exp (-ρ t)) t := by
  convert (hw.exp.sub_const 1).mul hρ.neg.exp using 1
  change L * Real.exp (-ρ t) =
      (Real.exp (w t) * (Real.exp (-w t) * L + (1 - Real.exp (-w t)) * R)) *
        Real.exp (-ρ t) + (Real.exp (w t) - 1) * (Real.exp (-ρ t) * -R)
  rw [show (Real.exp (w t) *
        (Real.exp (-w t) * L + (1 - Real.exp (-w t)) * R)) * Real.exp (-ρ t) +
        (Real.exp (w t) - 1) * (Real.exp (-ρ t) * -R) =
        (Real.exp (w t) * (Real.exp (-w t) * L + (1 - Real.exp (-w t)) * R) -
          (Real.exp (w t) - 1) * R) * Real.exp (-ρ t) by ring,
      nonlinear_exponential_cancellation]

theorem nonlinear_exponential_mass_bounds {w ρ : ℝ} (hw : 0 ≤ w) (hwρ : w ≤ ρ) :
    0 ≤ (Real.exp w - 1) * Real.exp (-ρ) ∧
      (Real.exp w - 1) * Real.exp (-ρ) ≤ 1 := by
  have hd := (Real.exp_pos (-ρ)).le
  refine ⟨mul_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hw)) hd, ?_⟩
  calc
    (Real.exp w - 1) * Real.exp (-ρ) ≤ Real.exp ρ * Real.exp (-ρ) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.exp_le_exp.mpr hwρ]) hd
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem self_le_exponential_sub_one (w : ℝ) : w ≤ Real.exp w - 1 := by
  linarith [Real.add_one_le_exp w]

end Yau.F04Proof
