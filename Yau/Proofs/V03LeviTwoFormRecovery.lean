import Yau.Proofs.V03LeviFormDiagonal

/-! The full complex Levi pairing is recovered from the actual native
real two-form; native two-form transport therefore transports every matrix entry. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem scalarLeviTwoForm_recover_mixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (u v : E) :
    wirt (fun y => wirtBar (fun x => (f x : ℂ)) y u) z v =
      ((scalarLeviTwoForm f z ![u, Complex.I • v] / 2 : ℝ) : ℂ) +
        Complex.I * ((scalarLeviTwoForm f z ![u, v] / 2 : ℝ) : ℂ) := by
  rw [scalarLeviTwoForm_apply hf, scalarLeviTwoForm_apply hf, leviTwoForm, leviTwoForm,
    wirt_smul_direction]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, one_mul, zero_add, add_zero, sub_zero] <;> ring

theorem scalarLevi_mixed_eq_of_twoForm_eq {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → ℝ} {g : F → ℝ} {z : E} {w : F}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g w) (A : E →L[ℂ] F)
    (he : scalarLeviTwoForm f z =
      (scalarLeviTwoForm g w).compContinuousLinearMap (A.restrictScalars ℝ)) (u v : E) :
    wirt (fun y => wirtBar (fun x => (f x : ℂ)) y u) z v =
      wirt (fun y => wirtBar (fun x => (g x : ℂ)) y (A u)) w (A v) := by
  rw [scalarLeviTwoForm_recover_mixed hf, scalarLeviTwoForm_recover_mixed hg,
    he, twoForm_pullback_apply, twoForm_pullback_apply]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul]

end Yau.Blueprint.V03Proof
