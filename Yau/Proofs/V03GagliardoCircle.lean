import Yau.Proofs.V03DifferenceKernel
import Yau.Proofs.V03FourierParsevalCircle

/-! The circular half-order seminorm is the actual nonnegative double
integral of squared difference quotients, with normalized Haar measure. -/

open scoped Topology
open MeasureTheory Filter AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

def circleDirichlet (u : AddCircle T → ℂ) : ENNReal :=
  ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| * ‖fourierCoeff u k‖ ^ 2)

def circleGagliardo (u : AddCircle T → ℂ) : ENNReal :=
  ∫⁻ a : AddCircle T, ∫⁻ x : AddCircle T,
    ENNReal.ofReal (‖u (x + a) - u x‖ ^ 2 / ‖fourier 1 a - 1‖ ^ 2)
    ∂haarAddCircle ∂haarAddCircle

theorem difference_quotient_parseval {u : AddCircle T → ℂ} (hu : Continuous u)
    (a : AddCircle T) :
    (∫⁻ x : AddCircle T,
      ENNReal.ofReal (‖u (x + a) - u x‖ ^ 2 / ‖fourier 1 a - 1‖ ^ 2) ∂haarAddCircle) =
      ∑' k : ℤ, ENNReal.ofReal (differenceKernel k a * ‖fourierCoeff u k‖ ^ 2) := by
  have hcont : Continuous (fun x => ‖u (x + a) - u x‖ ^ 2 / ‖fourier 1 a - 1‖ ^ 2) :=
    (((hu.comp (continuous_id.add continuous_const)).sub hu).norm.pow 2).div_const _
  have hInt : Integrable
      (fun x => ‖u (x + a) - u x‖ ^ 2 / ‖fourier 1 a - 1‖ ^ 2) haarAddCircle :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall (fun _ => by positivity)),
    integral_div]
  have hs := (circle_parseval_difference hu a).div_const (‖fourier 1 a - 1‖ ^ 2)
  have hs' : HasSum (fun k : ℤ => differenceKernel k a * ‖fourierCoeff u k‖ ^ 2)
      ((∫ x : AddCircle T, ‖u (x + a) - u x‖ ^ 2 ∂haarAddCircle) / ‖fourier 1 a - 1‖ ^ 2) := by
    convert hs using 1
    funext k
    unfold differenceKernel
    ring
  rw [← hs'.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by unfold differenceKernel; positivity)
    hs'.summable]

theorem circleGagliardo_eq_dirichlet {u : AddCircle T → ℂ} (hu : Continuous u) :
    circleGagliardo u = circleDirichlet u := by
  unfold circleGagliardo
  simp_rw [difference_quotient_parseval hu]
  have hmeas (k : ℤ) : AEMeasurable
      (fun a : AddCircle T => ENNReal.ofReal (differenceKernel k a * ‖fourierCoeff u k‖ ^ 2))
      haarAddCircle := by
    unfold differenceKernel
    fun_prop
  rw [lintegral_tsum hmeas]
  unfold circleDirichlet
  apply tsum_congr
  intro k
  have hInt := (differenceKernel_integrable (T := T) k).mul_const (‖fourierCoeff u k‖ ^ 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (Eventually.of_forall (fun a => by unfold differenceKernel; positivity)),
    integral_mul_const, differenceKernel_integral]

end Yau.Blueprint.V03Proof
