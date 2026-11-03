import Yau.Proofs.V03Fourier

/-! A genuinely periodic trace descends to the additive circle. Its native
circle coefficients are exactly the project's normalized coefficients. -/

open scoped Topology
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem periodic_lift_continuous {T : ℝ} {u : ℝ → ℂ}
    (hp : Function.Periodic u T) (hu : Continuous u) : Continuous hp.lift := by
  exact hu.quotient_lift _

theorem circleFourier_eq_periodic_lift {u : ℝ → ℂ}
    (hp : Function.Periodic u (2 * Real.pi)) (k : ℤ) :
    circleFourier u k = fourierCoeff hp.lift k := by
  rw [fourierCoeff_eq_intervalIntegral hp.lift k 0]
  simp only [zero_add, Function.Periodic.lift_coe, Complex.real_smul, smul_eq_mul,
    one_div, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
  unfold circleFourier
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [fourier_coe_apply, Int.cast_neg]
  congr 2
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  <;> ring

theorem circleDirichlet_periodic_lift {u : ℝ → ℂ}
    (hp : Function.Periodic u (2 * Real.pi)) :
    boundaryDSq (fun θ (_ : Unit) => u θ) =
      ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| * ‖fourierCoeff hp.lift k‖ ^ 2) := by
  simp only [boundaryDSq, Finset.univ_unique, Finset.sum_singleton,
    circleFourier_eq_periodic_lift hp, Int.cast_abs]

end Yau.Blueprint.V03Proof
