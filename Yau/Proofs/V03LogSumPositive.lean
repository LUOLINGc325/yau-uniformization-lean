import Yau.Proofs.V03LogSumLevi
import Yau.Proofs.V03FiniteCauchy
import Yau.Proofs.V03LeviLocality

/-! Semipositivity follows from the exact Levi formula and finite
Cauchy--Schwarz, retaining the original nested Wirtinger convention. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]

theorem log_holomorphicSqSum_levi_re {f : ι → E → ℂ} {z : E}
    (hf : ∀ i, ContDiffAt ℂ 2 (f i) z) (hs : holomorphicSqSum f z ≠ 0) (v : E) :
    (wirt (fun y => wirtBar (fun y' => (Real.log (holomorphicSqSum f y') : ℂ)) y v) z v).re =
      (holomorphicSqSum f z)⁻¹ * (∑ i, ‖fderiv ℂ (f i) z v‖ ^ 2) -
      (holomorphicSqSum f z)⁻¹ ^ 2 *
        ‖∑ i, star (f i z) * fderiv ℂ (f i) z v‖ ^ 2 := by
  let A : ℂ := ∑ i, star (f i z) * fderiv ℂ (f i) z v
  have hB : (∑ i, star (fderiv ℂ (f i) z v) * f i z) = star A := by
    simp only [A, star_sum, star_mul', star_star, mul_comm]
  have hprod : A * (∑ i, star (fderiv ℂ (f i) z v) * f i z) = (‖A‖ ^ 2 : ℝ) := by
    rw [hB, mul_comm]
    exact star_mul_self_eq_norm_sq A
  have hnorm : (∑ i, star (fderiv ℂ (f i) z v) * fderiv ℂ (f i) z v) =
      ((∑ i, ‖fderiv ℂ (f i) z v‖ ^ 2 : ℝ) : ℂ) := by
    simp only [star_mul_self_eq_norm_sq, Complex.ofReal_sum]
  have hm := log_holomorphicSqSum_levi hf hs v
  change _ = (holomorphicSqSum f z : ℂ)⁻¹ * _ -
    (holomorphicSqSum f z : ℂ)⁻¹ ^ 2 * A * _ at hm
  rw [hnorm, mul_assoc, hprod] at hm
  have hr := congrArg Complex.re hm
  simpa only [Complex.sub_re, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re, A] using hr

theorem log_holomorphicSqSum_levi_nonneg {f : ι → E → ℂ} {z : E}
    (hf : ∀ i, ContDiffAt ℂ 2 (f i) z) (hs : 0 < holomorphicSqSum f z) (v : E) :
    0 ≤ (wirt (fun y => wirtBar
      (fun y' => (Real.log (holomorphicSqSum f y') : ℂ)) y v) z v).re := by
  rw [log_holomorphicSqSum_levi_re hf hs.ne' v]
  have hcs := complex_sum_star_mul_norm_sq_le (fun i => f i z)
    (fun i => fderiv ℂ (f i) z v)
  change _ ≤ holomorphicSqSum f z * _ at hcs
  have hm := mul_le_mul_of_nonneg_left hcs (sq_nonneg ((holomorphicSqSum f z)⁻¹))
  have hc : (holomorphicSqSum f z)⁻¹ ^ 2 * holomorphicSqSum f z =
      (holomorphicSqSum f z)⁻¹ := by
    rw [pow_two, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
  rw [← mul_assoc, hc] at hm
  exact sub_nonneg.mpr hm

end Yau.Blueprint.V03Proof
