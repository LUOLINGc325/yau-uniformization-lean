import Yau.Proofs.V03Fourier

/-! Translation multipliers on the normalized additive circle. These are
native Fourier coefficients, including their full integral normalization. -/

open scoped Topology
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem fourier_point_add (k : ℤ) (x y : AddCircle T) :
    fourier k (x + y) = fourier k x * fourier k y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_point_norm (k : ℤ) (x : AddCircle T) : ‖fourier k x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

theorem fourierCoeff_translate (u : AddCircle T → ℂ) (a : AddCircle T) (k : ℤ) :
    fourierCoeff (fun x => u (x + a)) k = fourier k a * fourierCoeff u k := by
  have hunit : fourier k a * fourier (-k) a = 1 := by
    rw [← fourier_add]
    simp
  have hshift := integral_add_right_eq_self (μ := haarAddCircle)
    (fun x : AddCircle T => fourier k a * (fourier (-k) x * u x)) a
  calc
    fourierCoeff (fun x => u (x + a)) k =
        ∫ x : AddCircle T, fourier k a * (fourier (-k) (x + a) * u (x + a)) ∂haarAddCircle := by
      unfold fourierCoeff
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      simp only [smul_eq_mul, fourier_point_add]
      linear_combination -(fourier (-k) x * u (x + a)) * hunit
    _ = fourier k a * fourierCoeff u k := by
      rw [hshift, integral_const_mul]
      rfl

theorem fourierCoeff_translate_sub {u : AddCircle T → ℂ} (hu : Continuous u)
    (a : AddCircle T) (k : ℤ) :
    fourierCoeff (fun x => u (x + a) - u x) k = (fourier k a - 1) * fourierCoeff u k := by
  have hshift : Continuous (fun x => u (x + a)) := hu.comp (continuous_id.add continuous_const)
  have hsum := congrArg (fun f : ℤ → ℂ => f k)
    (fourierCoeff.add (hshift.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hu.neg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)))
  change fourierCoeff (fun x => u (x + a) + -u x) k =
    fourierCoeff (fun x => u (x + a)) k + fourierCoeff (fun x => -u x) k at hsum
  have hneg := fourierCoeff.const_mul u (-1) k
  rw [show (fun x => -u x) = (fun x => (-1 : ℂ) * u x) by funext x; ring, hneg,
    fourierCoeff_translate] at hsum
  simpa only [sub_eq_add_neg] using hsum.trans (by ring)

end Yau.Blueprint.V03Proof
