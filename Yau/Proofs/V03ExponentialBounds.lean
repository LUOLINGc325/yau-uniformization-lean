import Yau.Proofs.V03BoundaryDifference
import Yau.Proofs.V03LogTrace

/-! Exponential phase and nonpositive real exponential maps have the
uniform Lipschitz bounds required by the actual half-order wall energy. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circlePoint_sub_norm_le (x y : ℝ) : ‖circlePoint x - circlePoint y‖ ≤ |x - y| := by
  have heq : circlePoint x - circlePoint y = circlePoint y * (circlePoint (x - y) - 1) := by
    unfold circlePoint
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  rw [heq, norm_mul, circlePoint_norm, one_mul]
  simpa only [circlePoint, mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

theorem boundaryDSq_exp_phase_le {q : ℝ → ℝ} (hq : Continuous q)
    (hp : Function.Periodic q (2 * Real.pi)) (a : ℝ) :
    boundaryDSq (fun θ (_ : Unit) => circlePoint (a * q θ)) ≤
      ENNReal.ofReal (a ^ 2) * scalarDSq q := by
  have hu : Continuous (fun θ => (q θ : ℂ)) := Complex.continuous_ofReal.comp hq
  have hv : Continuous (fun θ => circlePoint (a * q θ)) :=
    circlePoint_contDiff.continuous.comp (continuous_const.mul hq)
  have hup : Function.Periodic (fun θ => (q θ : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg Complex.ofReal (hp θ)
  have hvp : Function.Periodic (fun θ => circlePoint (a * q θ)) (2 * Real.pi) :=
    fun θ => congrArg (fun t => circlePoint (a * t)) (hp θ)
  have hb (θ t : ℝ) : ‖circlePoint (a * q θ) - circlePoint (a * q t)‖ ≤
      |a| * ‖(q θ : ℂ) - (q t : ℂ)‖ := by
    have hh := circlePoint_sub_norm_le (a * q θ) (a * q t)
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      ← mul_sub, abs_mul] using hh
  simpa only [sq_abs, scalarDSq] using boundaryDSq_le_of_difference_bound hu hv hup hvp (abs_nonneg a) hb

theorem exp_mul_sub_le_of_nonpos {a x y : ℝ} (ha : 0 ≤ a) (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp (a * x) - Real.exp (a * y)| ≤ a * |x - y| := by
  have hd (t : ℝ) : HasDerivAt (fun r => Real.exp (a * r)) (Real.exp (a * t) * a) t :=
    by simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul a).exp
  have hb (t : ℝ) (ht : t ∈ Set.Iic 0) : ‖Real.exp (a * t) * a‖ ≤ a := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le ha)]
    have he : Real.exp (a * t) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha ht)
    nlinarith
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Set.Iic (0 : ℝ)) => (hd t).hasDerivWithinAt) hb (convex_Iic (0 : ℝ)) hy hx

theorem scalarDSq_exp_nonpos_le {q : ℝ → ℝ} (hq : Continuous q)
    (hp : Function.Periodic q (2 * Real.pi)) (hq0 : ∀ θ, q θ ≤ 0)
    {a : ℝ} (ha : 0 ≤ a) :
    scalarDSq (fun θ => Real.exp (a * q θ)) ≤ ENNReal.ofReal (a ^ 2) * scalarDSq q := by
  have hu : Continuous (fun θ => (q θ : ℂ)) := Complex.continuous_ofReal.comp hq
  have hv : Continuous (fun θ => (Real.exp (a * q θ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hq))
  have hup : Function.Periodic (fun θ => (q θ : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg Complex.ofReal (hp θ)
  have hvp : Function.Periodic (fun θ => (Real.exp (a * q θ) : ℂ)) (2 * Real.pi) :=
    fun θ => congrArg (fun t => (Real.exp (a * t) : ℂ)) (hp θ)
  unfold scalarDSq
  apply boundaryDSq_le_of_difference_bound hu hv hup hvp ha
  intro θ t
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
    exp_mul_sub_le_of_nonpos ha (hq0 θ) (hq0 t)

end Yau.Blueprint.V03Proof
