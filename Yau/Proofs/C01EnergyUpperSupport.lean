import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The square root of the genuine energy is a differentiable upper
support for the first-exit distance minimum. Only the energy at the
current minimizing path is required to be strictly positive. -/

noncomputable section
open scoped Topology

namespace Yau.NodeProofs.C01Aux

theorem energy_sqrt_upperTouch
    (l E : ℝ → ℝ) (J : Set ℝ) (a d I : ℝ) (hd : 0 < d)
    (hla : l a = d) (hEa : E a = d ^ 2)
    (hupper : ∀ u ∈ J, l u ^ 2 ≤ E u) (hE : HasDerivAt E (-I) a) :
    Real.sqrt (E a) = l a ∧ (∀ u ∈ J, l u ≤ Real.sqrt (E u)) ∧
      HasDerivAt (fun u => Real.sqrt (E u)) (-I / (2 * d)) a := by
  have hroot : Real.sqrt (E a) = d := by rw [hEa, Real.sqrt_sq hd.le]
  have hEne : E a ≠ 0 := by rw [hEa]; exact (sq_pos_of_pos hd).ne'
  refine ⟨hroot.trans hla.symm, fun u hu => Real.le_sqrt_of_sq_le (hupper u hu), ?_⟩
  have HD := (Real.hasDerivAt_sqrt hEne).comp a hE
  rw [hroot] at HD
  have hcoeff : (1 / (2 * d)) * (-I) = -I / (2 * d) := by ring
  rw [hcoeff] at HD
  exact HD

end Yau.NodeProofs.C01Aux
