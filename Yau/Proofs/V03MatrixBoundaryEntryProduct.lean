import Yau.Proofs.V03BoundarySum
import Yau.Proofs.V03BoundaryVectorProduct

/-! Individual coefficients and actual triple products are controlled by
the original summed Fourier seminorms, with all infinite endpoints retained. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem matrixDSq_entry_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ℝ → Matrix ι κ ℂ) (i : ι) (j : κ) :
    boundaryDSq (fun θ (_ : Unit) => A θ i j) ≤ matrixDSq A := by
  classical
  simp only [matrixDSq, boundaryDSq, Finset.univ_unique, Finset.sum_singleton]
  exact Finset.single_le_sum
    (f := fun ij : ι × κ => ∑' k : ℤ,
      ENNReal.ofReal ((|k| : ℤ) * ‖circleFourier (fun θ => A θ ij.1 ij.2) k‖ ^ 2))
    (s := Finset.univ) (a := (i, j)) (fun _ _ => bot_le) (Finset.mem_univ _)

theorem boundaryDSq_triple_le {u v w : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hup : Function.Periodic u (2 * Real.pi))
    (hvp : Function.Periodic v (2 * Real.pi))
    (hwp : Function.Periodic w (2 * Real.pi))
    {M : ℝ} (hM : 0 ≤ M) (hu1 : ∀ θ, ‖u θ‖ ≤ 1)
    (hvM : ∀ θ, ‖v θ‖ ≤ M) (hw1 : ∀ θ, ‖w θ‖ ≤ 1) :
    boundaryDSq (fun θ (_ : Unit) => star (u θ) * v θ * w θ) ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal (2 * M ^ 2) *
        boundaryDSq (fun θ (_ : Unit) => u θ) +
          ENNReal.ofReal 2 * boundaryDSq (fun θ (_ : Unit) => v θ)) +
      ENNReal.ofReal (2 * M ^ 2) * boundaryDSq (fun θ (_ : Unit) => w θ) := by
  have hc : Continuous (fun θ => star (u θ)) := hu.star
  have hcp : Function.Periodic (fun θ => star (u θ)) (2 * Real.pi) :=
    fun θ => congrArg star (hup θ)
  have hcn : ∀ θ, ‖star (u θ)‖ ≤ 1 := by simpa only [norm_star] using hu1
  have huv := boundaryDSq_mul_le hc hv hcp hvp (by norm_num : (0 : ℝ) ≤ 1) hM hcn hvM
  rw [scalarDSq_conj hu hup] at huv
  simp only [one_pow, mul_one] at huv
  have hprod : ∀ θ, ‖star (u θ) * v θ‖ ≤ M := by
    intro θ
    rw [norm_mul]
    exact (mul_le_mul (hcn θ) (hvM θ) (norm_nonneg _) (by norm_num)).trans_eq (one_mul M)
  have hh := boundaryDSq_mul_le (hc.mul hv) hw (hcp.mul hvp) hwp hM
    (by norm_num : (0 : ℝ) ≤ 1) hprod hw1
  simp only [one_pow, mul_one] at hh
  apply hh.trans
  gcongr
  exact huv

end Yau.Blueprint.V03Proof
