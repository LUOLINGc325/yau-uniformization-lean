import Yau.Proofs.V03Fourier

/-! The exact integer weight in the circular difference-quotient kernel
comes from the norm of a finite orthonormal Fourier sum. -/

open scoped Topology ComplexConjugate
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

def geometricFourier (m : ℕ) : C(AddCircle T, ℂ) :=
  ∑ j ∈ Finset.range m, fourier (j : ℤ)

theorem geometricFourier_integral_norm_sq (m : ℕ) :
    (∫ x : AddCircle T, ‖geometricFourier m x‖ ^ 2 ∂haarAddCircle) = (m : ℝ) := by
  have hOrth : Orthonormal ℂ (fun j : ℕ => (fourierLp (T := T) 2 (j : ℤ))) :=
    orthonormal_fourier.comp (fun j : ℕ => (j : ℤ)) Int.ofNat_injective
  have hc := hOrth.inner_sum (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) (Finset.range m)
  simp only [one_smul, map_one, one_mul, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hc
  have hi : inner ℂ (ContinuousMap.toLp 2 haarAddCircle ℂ (geometricFourier (T := T) m))
      (ContinuousMap.toLp 2 haarAddCircle ℂ (geometricFourier (T := T) m)) = (m : ℂ) := by
    simpa only [geometricFourier, map_sum, fourierLp] using hc
  rw [ContinuousMap.inner_toLp] at hi
  simp_rw [Complex.mul_conj'] at hi
  simp only [← Complex.ofReal_pow] at hi
  rw [integral_complex_ofReal] at hi
  exact_mod_cast hi

theorem fourier_nat_pow (m : ℕ) (x : AddCircle T) :
    fourier (m : ℤ) x = (fourier 1 x) ^ m := by
  simp only [fourier_apply, natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow,
    one_zsmul]

theorem geometricFourier_mul (m : ℕ) (x : AddCircle T) :
    geometricFourier m x * (fourier 1 x - 1) = fourier (m : ℤ) x - 1 := by
  simp only [geometricFourier, ContinuousMap.sum_apply, fourier_nat_pow]
  exact geom_sum_mul (fourier 1 x) m

end Yau.Blueprint.V03Proof
