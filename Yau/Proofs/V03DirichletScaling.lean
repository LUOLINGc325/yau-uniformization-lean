import Yau.Proofs.V03Dirichlet

/-! Exact homogeneity of the original computed Fourier seminorm, including
infinite values, and the actual logarithmic wall-power trace. -/

open scoped Topology
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_const_mul {ι : Type*} [Fintype ι] (u : ℝ → ι → ℂ) (c : ℂ) :
    boundaryDSq (fun θ i => c * u θ i) = ENNReal.ofReal (‖c‖ ^ 2) * boundaryDSq u := by
  unfold boundaryDSq
  simp only [circleFourier_const_mul, norm_mul, mul_pow]
  have hf (k : ℤ) (i : ι) :
      ENNReal.ofReal (|k| * (‖c‖ ^ 2 * ‖circleFourier (fun θ => u θ i) k‖ ^ 2)) =
        ENNReal.ofReal (‖c‖ ^ 2) *
          ENNReal.ofReal (|k| * ‖circleFourier (fun θ => u θ i) k‖ ^ 2) := by
    rw [mul_left_comm, ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
  simp_rw [hf, ENNReal.tsum_mul_left]
  rw [Finset.mul_sum]

theorem scalarDSq_const_mul (u : ℝ → ℝ) (c : ℝ) :
    scalarDSq (fun θ => c * u θ) = ENNReal.ofReal (c ^ 2) * scalarDSq u := by
  unfold scalarDSq
  simp only [Complex.ofReal_mul]
  have hh := boundaryDSq_const_mul (fun θ (_ : Unit) => (u θ : ℂ)) (c : ℂ)
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh

theorem scalarDSq_log_wallPower {n q : ℕ} {X : KahlerManifold n}
    (d : VariationData X q) (j a : ℕ) (F : VariationDisc X) :
    scalarDSq (fun θ => Real.log (wallPower d j a (F.f (circlePoint θ)))) =
      ENNReal.ofReal ((a : ℝ) ^ 2) *
        scalarDSq (fun θ => Real.log (wallProduct d j (F.f (circlePoint θ)))) := by
  simp only [wallPower, Real.log_pow]
  exact scalarDSq_const_mul _ (a : ℝ)

end Yau.Blueprint.V03Proof
