import Yau.Proofs.V04SpectralLipschitz
import Yau.Proofs.V04SmoothSqrtMajorant
import Yau.Proofs.V04MatrixGagliardo

/-! The exact regularized majorant has the sharp Frobenius contraction
and hence the exact original Fourier-seminorm contraction. Smoothness is
that of the same spectral expression proved by the local square inverse. -/

open scoped Matrix ComplexOrder MatrixOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

theorem scalarRoot_abs_sub_le (δ x y : ℝ) :
    |Real.sqrt (x ^ 2 + δ ^ 2) - Real.sqrt (y ^ 2 + δ ^ 2)| ≤ |x - y| := by
  let z : ℝ → ℂ := fun t => ⟨t, δ⟩
  have hn (t : ℝ) : ‖z t‖ = Real.sqrt (t ^ 2 + δ ^ 2) := by
    simp only [Complex.norm_def, Complex.normSq_apply, z, pow_two]
  have heq : z x - z y = ((x - y : ℝ) : ℂ) := by apply Complex.ext <;> simp [z]
  have hh := abs_norm_sub_norm_le (z x) (z y)
  rw [hn x, hn y, heq, Complex.norm_real, Real.norm_eq_abs] at hh
  exact hh

theorem scalarMajorant_abs_sub_le (δ x y : ℝ) :
    |scalarMajorant δ x - scalarMajorant δ y| ≤ |x - y| := by
  have hs := scalarRoot_abs_sub_le δ x y
  have ht := abs_add_le (x - y)
    (Real.sqrt (x ^ 2 + δ ^ 2) - Real.sqrt (y ^ 2 + δ ^ 2))
  have heq : scalarMajorant δ x - scalarMajorant δ y =
      ((x - y) + (Real.sqrt (x ^ 2 + δ ^ 2) - Real.sqrt (y ^ 2 + δ ^ 2))) / 2 := by
    unfold scalarMajorant
    ring
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith only [hs, ht]

variable {n : ℕ}

theorem smoothMajorant_frobSq_sub_le (δ : ℝ) (A B : CotangentMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    matrixFrobSq (smoothMajorant δ A - smoothMajorant δ B) ≤ matrixFrobSq (A - B) := by
  change matrixFrobSq (hermitianScalar (scalarMajorant δ) A -
    hermitianScalar (scalarMajorant δ) B) ≤ matrixFrobSq (A - B)
  simpa only [one_pow, one_mul] using
    hermitianScalar_frobSq_lipschitz (scalarMajorant δ) (L := 1) zero_le_one
      (fun x y => by simpa only [one_mul] using scalarMajorant_abs_sub_le δ x y) A B hA hB

theorem matrixDSq_smoothMajorant_le {δ : ℝ} (hδ : 0 < δ)
    {A : ℝ → CotangentMatrix n}
    (hA : ∀ i k, ContDiff ℝ ∞ (fun θ => A θ i k))
    (hAp : Function.Periodic A (2 * Real.pi)) (hHerm : ∀ θ, (A θ).IsHermitian) :
    matrixDSq (fun θ => smoothMajorant δ (A θ)) ≤ matrixDSq A := by
  apply boundaryDSq_le_of_square_sum_bound
    (u := fun θ (p : CotangentIndex n × CotangentIndex n) => A θ p.1 p.2)
    (v := fun θ (p : CotangentIndex n × CotangentIndex n) => smoothMajorant δ (A θ) p.1 p.2)
    (fun p => (hA p.1 p.2).continuous)
    (fun p => (smoothMajorant_entry_contDiff hδ A hA hHerm p.1 p.2).continuous)
    (fun p θ => congrFun (congrFun (hAp θ) p.1) p.2)
    (fun p θ => congrFun (congrFun (congrArg (smoothMajorant δ) (hAp θ)) p.1) p.2)
  intro θ t
  simpa only [Fintype.sum_prod_type, Matrix.sub_apply, matrixFrobSq] using
    smoothMajorant_frobSq_sub_le δ (A θ) (A t) (hHerm θ) (hHerm t)

end Yau.Blueprint.V04Proof
