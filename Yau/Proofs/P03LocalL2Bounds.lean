import Yau.Proofs.P03Measure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Topology ENNReal
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

theorem integral_norm_le_sqrt_L2 {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsFiniteMeasure ν] {f : A → ℂ} (hf : MemLp f 2 ν) :
    (∫ x, ‖f x‖ ∂ν) ≤ Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂ν) * Real.sqrt (ν.real Set.univ) := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) ν := by simpa using hf
  have h1 : MemLp (fun _ : A => (1 : ℂ)) (ENNReal.ofReal (2 : ℝ)) ν := memLp_const 1
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf' h1
  simpa only [norm_one, mul_one, Real.rpow_two, one_pow, integral_const,
    smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] using hh

theorem complexVector_real_dimension (n : ℕ) : Module.finrank ℝ (ComplexVector n) = 2 * n := by
  rw [finrank_real_of_complex]
  simp [ComplexVector]

theorem sqrt_volume_closedBall {n : ℕ} (a : ComplexVector n) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt ((volume : Measure (ComplexVector n)).real (Metric.closedBall a t)) =
      t ^ n * Real.sqrt ((volume : Measure (ComplexVector n)).real (Metric.closedBall 0 1)) := by
  rw [Measure.addHaar_real_closedBall' volume a ht, complexVector_real_dimension,
    Real.sqrt_mul (pow_nonneg ht _)]
  congr 1
  rw [mul_comm 2 n, pow_mul, Real.sqrt_sq (pow_nonneg ht n)]

end Yau.NodeProofs.P03Aux
