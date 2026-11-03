import Yau.Proofs.V03GagliardoLipschitz
import Yau.Proofs.V03DirichletScaling
import Yau.Proofs.V03BoundaryDifference

/-! Real projection is a contraction for the original half-order
seminorm; the actual first-real-jet factor two is retained. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_real_part_le {u : ℝ → ℂ} (hu : Continuous u)
    (hp : Function.Periodic u (2 * Real.pi)) :
    scalarDSq (fun θ => (u θ).re) ≤ boundaryDSq (fun θ (_ : Unit) => u θ) := by
  have hrc : Continuous (fun θ => ((u θ).re : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp hu)
  have hrp : Function.Periodic (fun θ => ((u θ).re : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg (fun z : ℂ => (z.re : ℂ)) (hp θ)
  have hb := boundaryDSq_le_of_difference_bound hu hrc hp hrp (C := 1) (by norm_num)
    (fun θ τ => by
      rw [one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← Complex.sub_re]
      exact Complex.abs_re_le_norm _)
  simpa only [one_pow, ENNReal.ofReal_one, one_mul, scalarDSq] using hb

theorem boundaryDSq_two_re_mul_le {u : ℝ → ℂ} (hu : Continuous u)
    (hp : Function.Periodic u (2 * Real.pi)) (v : ℂ) (hv : ‖v‖ ≤ 1) :
    scalarDSq (fun θ => 2 * (v * u θ).re) ≤ 4 * boundaryDSq (fun θ (_ : Unit) => u θ) := by
  rw [scalarDSq_const_mul]
  norm_num only [OfNat.ofNat_ne_zero, ENNReal.ofReal_ofNat, Nat.reducePow]
  have hvc : Continuous (fun θ => v * u θ) := continuous_const.mul hu
  have hvp : Function.Periodic (fun θ => v * u θ) (2 * Real.pi) :=
    fun θ => congrArg (v * ·) (hp θ)
  have hb := boundaryDSq_real_part_le hvc hvp
  rw [boundaryDSq_const_mul] at hb
  calc
    _ ≤ 4 * (ENNReal.ofReal (‖v‖ ^ 2) * boundaryDSq (fun θ (_ : Unit) => u θ)) := by gcongr
    _ ≤ 4 * boundaryDSq (fun θ (_ : Unit) => u θ) := by
      have hsq : ‖v‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg v]
      have hn : ENNReal.ofReal (‖v‖ ^ 2) ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hsq
      calc
        _ ≤ 4 * (1 * boundaryDSq (fun θ (_ : Unit) => u θ)) := by gcongr
        _ = _ := by rw [one_mul]

end Yau.Blueprint.V03Proof
