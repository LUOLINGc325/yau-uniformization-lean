import Yau.Proofs.V03FourierFunctional
import Yau.Proofs.V03FourierConjugate

/-! Exact native Fourier calculus for constant traces and the imaginary
part of a complex continuous trace. -/

open scoped Topology ComplexConjugate
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem fourierCoeff_const_value (c : ℂ) (k : ℤ) :
    fourierCoeff (fun _ : AddCircle T => c) k = if k = 0 then c else 0 := by
  have hf : (fun _ : AddCircle T => c) = fun x => c * fourier 0 x := by
    funext x
    simp
  rw [hf, fourierCoeff.const_mul, fourierCoeff_fourier]
  simp [Pi.single_apply, eq_comm]

theorem fourierCoeff_imaginary (f : C(AddCircle T, ℂ)) (k : ℤ) :
    fourierCoeff (fun x => ((f x).im : ℂ)) k =
      (fourierCoeff (f : AddCircle T → ℂ) k - conj (fourierCoeff (f : AddCircle T → ℂ) (-k))) /
        (2 * Complex.I) := by
  let g : C(AddCircle T, ℂ) := ⟨fun x => ((f x).im : ℂ),
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp f.continuous)⟩
  have hg : g = (1 / (2 * Complex.I) : ℂ) • (f - star f) := by
    ext x
    change ((f x).im : ℂ) = (1 / (2 * Complex.I)) * (f x - conj (f x))
    rw [Complex.im_eq_sub_conj]
    ring
  have hstar : ((star f : C(AddCircle T, ℂ)) : AddCircle T → ℂ) = fun x => conj (f x) := rfl
  change fourierCoeffFunctional k g = _
  rw [hg, map_smul, map_sub, fourierCoeffFunctional_apply, fourierCoeffFunctional_apply,
    hstar, fourierCoeff_conj]
  simp only [smul_eq_mul, div_eq_mul_inv, one_mul]
  ring

end Yau.Blueprint.V03Proof
