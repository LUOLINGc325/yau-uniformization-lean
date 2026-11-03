import Yau.Proofs.V03FourierTranslation

/-! Parseval for continuous circle traces and their translated differences,
with normalized Haar measure and the exact Fourier multiplier. -/

open scoped Topology
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

theorem circle_parseval_continuous {u : AddCircle T → ℂ} (hu : Continuous u) :
    HasSum (fun k : ℤ => ‖fourierCoeff u k‖ ^ 2)
      (∫ x : AddCircle T, ‖u x‖ ^ 2 ∂haarAddCircle) := by
  let f : C(AddCircle T, ℂ) := ⟨u, hu⟩
  have hfu : (f : AddCircle T → ℂ) = u := rfl
  have hs := hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 haarAddCircle ℂ f)
  have haeq := f.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle
  have hi : (∫ x : AddCircle T, ‖ContinuousMap.toLp 2 haarAddCircle ℂ f x‖ ^ 2 ∂haarAddCircle) =
      ∫ x : AddCircle T, ‖u x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    exact haeq.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx
  simpa only [fourierCoeff_toLp, hi, hfu] using hs

theorem circle_parseval_difference {u : AddCircle T → ℂ} (hu : Continuous u)
    (a : AddCircle T) :
    HasSum (fun k : ℤ => ‖fourier k a - 1‖ ^ 2 * ‖fourierCoeff u k‖ ^ 2)
      (∫ x : AddCircle T, ‖u (x + a) - u x‖ ^ 2 ∂haarAddCircle) := by
  have hc : Continuous (fun x => u (x + a) - u x) :=
    (hu.comp (continuous_id.add continuous_const)).sub hu
  have hs := circle_parseval_continuous hc
  simpa only [fourierCoeff_translate_sub hu, norm_mul, mul_pow] using hs

end Yau.Blueprint.V03Proof
