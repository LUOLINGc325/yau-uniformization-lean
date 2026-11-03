import Yau.Proofs.D06HardyEvaluation
import Yau.Proofs.D06HardyCoordinates

/-! Actual Hardy reproducing kernels, with exact dimension-free norm. -/

open scoped ComplexConjugate lp

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def hardyKernelFn (z : ℂ) (v : EuclideanSpace ℂ (Fin r)) (k : ℕ × Fin r) : ℂ :=
  conj z ^ k.1 * v k.2

theorem hardyKernel_summable (z : ℂ) (hz : ‖z‖ < 1) (v : EuclideanSpace ℂ (Fin r)) :
    Summable (fun k : ℕ × Fin r => ‖hardyKernelFn z v k‖ ^ 2) := by
  have hs : Summable (fun n : ℕ => (‖z‖ ^ 2) ^ n) :=
    summable_geometric_of_lt_one (sq_nonneg _) (by nlinarith [norm_nonneg z])
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  constructor
  · intro n
    exact (hasSum_fintype _).summable
  · simp only [hardyKernelFn, norm_mul, norm_pow, Complex.norm_conj, mul_pow, pow_right_comm ‖z‖ _ 2, tsum_fintype, ← Finset.mul_sum]
    exact hs.mul_right _

def hardyKernel (z : ℂ) (hz : ‖z‖ < 1) (v : EuclideanSpace ℂ (Fin r)) : HardySeq r :=
  ⟨hardyKernelFn z v, memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hardyKernel_summable z hz v)⟩

@[simp] theorem hardyKernel_apply (z : ℂ) (hz : ‖z‖ < 1)
    (v : EuclideanSpace ℂ (Fin r)) (n : ℕ) (j : Fin r) :
    hardyKernel z hz v (n, j) = conj z ^ n * v j := rfl

theorem hardyKernel_norm_sq (z : ℂ) (hz : ‖z‖ < 1) (v : EuclideanSpace ℂ (Fin r)) :
    ‖hardyKernel z hz v‖ ^ 2 = (1 - ‖z‖ ^ 2)⁻¹ * ‖v‖ ^ 2 := by
  have hn : ‖hardyKernel z hz v‖ ^ 2 =
      ∑' k : ℕ × Fin r, ‖hardyKernel z hz v k‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := 2) (by norm_num) (hardyKernel z hz v)).tsum_eq.symm
  rw [hn, (hardy_summable_norm_sq (hardyKernel z hz v)).tsum_prod]
  simp only [hardyKernel_apply, norm_mul, norm_pow, Complex.norm_conj, mul_pow,
    pow_right_comm ‖z‖ _ 2, tsum_fintype, ← Finset.mul_sum]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (sq_nonneg _) (by nlinarith [norm_nonneg z]),
    EuclideanSpace.norm_sq_eq]

theorem hardyKernel_reproduces (z : ℂ) (hz : ‖z‖ < 1)
    (v : EuclideanSpace ℂ (Fin r)) (a : HardySeq r) :
    inner ℂ (hardyKernel z hz v) a = inner ℂ v (hardyEval a z) := by
  let f : ℕ → Fin r → ℂ := fun n j => inner ℂ (hardyKernel z hz v (n, j)) (a (n, j))
  have hs : Summable (Function.uncurry f) := lp.summable_inner (hardyKernel z hz v) a
  have hp : inner ℂ (hardyKernel z hz v) a = ∑' n : ℕ, ∑' j : Fin r, f n j := hs.tsum_prod
  have hc : (∑' n : ℕ, ∑' j : Fin r, f n j) = ∑' j : Fin r, ∑' n : ℕ, f n j := hs.tsum_comm.symm
  rw [hp, hc, tsum_fintype, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  change (∑' n : ℕ, inner ℂ (conj z ^ n * v j) (a (n, j))) =
    inner ℂ (v j) (hardyEvalEntry a j z)
  simp only [RCLike.inner_apply', map_mul, map_pow, Complex.conj_conj]
  rw [hardyEvalEntry_eq_tsum, ← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

end Yau.NodeProofs.D06Aux
