import Yau.Proofs.P04FiniteGram

noncomputable section
open WithLp
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau

/-- The actual finite vector whose squared norm is the selected partial sum. -/
def finiteCoefficientVector {n : ℕ} (N : ℕ) (c : ℕ → ℝ)
    (f : ℕ → ComplexVector n → ℂ) (z : ComplexVector n) : ComplexVector N :=
  toLp 2 (fun i : Fin N => (Real.sqrt (c i) : ℂ)*f i z)

theorem finiteCoefficientVector_contDiffAt {n N : ℕ} (c : ℕ → ℝ)
    (f : ℕ → ComplexVector n → ℂ) {z : ComplexVector n}
    (hf : ∀ i < N, ContDiffAt ℂ 2 (f i) z) :
    ContDiffAt ℂ 2 (finiteCoefficientVector N c f) z := by
  apply (contDiffAt_piLp 2).mpr
  intro i
  change ContDiffAt ℂ 2 (fun y => (Real.sqrt (c i) : ℂ)*f i y) z
  exact contDiffAt_const.mul (hf i i.isLt)

theorem finiteCoefficientVector_norm_sq {n : ℕ} (N : ℕ) (c : ℕ → ℝ)
    (f : ℕ → ComplexVector n → ℂ) (hc : ∀ i, 0 ≤ c i) (z : ComplexVector n) :
    ‖finiteCoefficientVector N c f z‖^2 = ∑ i ∈ Finset.range N, c i*‖f i z‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ = ∑ i : Fin N, c i*‖f i z‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      change ‖(Real.sqrt (c i) : ℂ)*f i z‖^2 = _
      rw [norm_mul,mul_pow]
      have hs : ‖(Real.sqrt (c i) : ℂ)‖^2=c i := by
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] using
          Real.sq_sqrt (hc i)
      rw [hs]
    _ = _ := Fin.sum_univ_eq_sum_range (fun i => c i*‖f i z‖^2) N

end Yau.Proofs.P04Aux
