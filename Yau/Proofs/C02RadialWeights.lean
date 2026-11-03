import spec.CHAIN.CONTRACTS
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact radial integration gains used by the differentiated connection and
torsion homotopies. The denominators retain one common geometric radius. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Interval
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_integral_radial_weights (m : ℕ) (F : ℝ → E) (a b : ℝ)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖F t‖ ≤ a * t ^ (m + 1) + (m : ℝ) * b * t ^ m) :
    ‖∫ t in (0 : ℝ)..1, F t‖ ≤ a / (m + 2) + (m : ℝ) / (m + 1) * b := by
  have hA : IntervalIntegrable (fun t : ℝ => a * t ^ (m + 1)) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow (m + 1))).intervalIntegrable 0 1
  have hB : IntervalIntegrable (fun t : ℝ => ((m : ℝ) * b) * t ^ m) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow m)).intervalIntegrable 0 1
  calc
    ‖∫ t in (0 : ℝ)..1, F t‖ ≤
        ∫ t in (0 : ℝ)..1, (a * t ^ (m + 1) + ((m : ℝ) * b) * t ^ m) :=
      intervalIntegral.norm_integral_le_of_norm_le zero_le_one
        (Eventually.of_forall (fun t ht => hF t ⟨ht.1.le, ht.2⟩)) (hA.add hB)
    _ = a / (m + 2) + (m : ℝ) / (m + 1) * b := by
      rw [intervalIntegral.integral_add hA hB,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      simp only [integral_pow, one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
      push_cast
      ring

end Yau.Blueprint.C02Proof
