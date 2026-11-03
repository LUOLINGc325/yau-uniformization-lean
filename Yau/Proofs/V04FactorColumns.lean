import Yau.Proofs.V04FactorTransport

/-! A constant Euclidean direction may depend on the disc. Its inverse
factor column satisfies the exact sup and Fourier-energy requirements of
DeformationEstimate, with no dimension loss and no infinite-toReal shortcut. -/

open scoped Matrix ComplexOrder Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem matrix_vector_norm_sq_le_frob (A : CotangentMatrix n)
    (v : EuclideanSpace ℂ (CotangentIndex n)) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 ≤ matrixFrobSq A * ‖v‖ ^ 2 := by
  have hrow (i : CotangentIndex n) :
      ‖∑ j, A i j * v j‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * ‖v‖ ^ 2 := by
    have habs : ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
      simpa only [norm_mul] using (norm_sum_le Finset.univ (fun j => A i j * v j))
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr habs
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j => ‖A i j‖) (fun j => ‖v j‖)
    rw [← EuclideanSpace.norm_sq_eq v] at hcs
    exact hsq.trans hcs
  calc
    _ = ∑ i, ‖∑ j, A i j * v j‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    _ ≤ ∑ i, (∑ j, ‖A i j‖ ^ 2) * ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem boundaryDSq_eq_tsum_vector_fourier (u : ℝ → CotangentIndex n → ℂ) :
    boundaryDSq u = ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| *
      ‖(WithLp.toLp 2 (fun i => circleFourier (fun θ => u θ i) k) :
        EuclideanSpace ℂ (CotangentIndex n))‖ ^ 2) := by
  calc
    boundaryDSq u = ∑' i : CotangentIndex n, ∑' k : ℤ,
        ENNReal.ofReal (|(k : ℝ)| * ‖circleFourier (fun θ => u θ i) k‖ ^ 2) := by
      rw [boundaryDSq, tsum_fintype]
      simp only [Int.cast_abs]
    _ = ∑' k : ℤ, ∑' i : CotangentIndex n,
        ENNReal.ofReal (|(k : ℝ)| * ‖circleFourier (fun θ => u θ i) k‖ ^ 2) :=
      ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      congr 1
      simp only [EuclideanSpace.norm_sq_eq, Finset.mul_sum]

theorem circleFourier_matrix_mulVec_const (A : ℝ → CotangentMatrix n)
    (v : CotangentIndex n → ℂ) (hA : ∀ i j, Continuous (fun θ => A θ i j)) (k : ℤ) :
    (fun i => circleFourier (fun θ => (A θ *ᵥ v) i) k) =
      (show CotangentMatrix n from fun i j => circleFourier (fun θ => A θ i j) k) *ᵥ v := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [circleFourier_finite_sum Finset.univ (fun l θ => A θ i l * v l)
    (fun l => (hA i l).mul continuous_const)]
  exact Finset.sum_congr rfl (fun l _ => circleFourier_mul_const _ _ k)

theorem boundaryDSq_matrix_constant_column_le (A : ℝ → CotangentMatrix n)
    (v : EuclideanSpace ℂ (CotangentIndex n))
    (hA : ∀ i j, Continuous (fun θ => A θ i j)) :
    boundaryDSq (fun θ => A θ *ᵥ WithLp.ofLp v) ≤
      ENNReal.ofReal (‖v‖ ^ 2) * matrixDSq A := by
  rw [boundaryDSq_eq_tsum_vector_fourier, matrixDSq_eq_tsum_frob_fourier,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro k
  rw [circleFourier_matrix_mulVec_const A (WithLp.ofLp v) hA k]
  let M : CotangentMatrix n := fun i j => circleFourier (fun θ => A θ i j) k
  change ENNReal.ofReal (|(k : ℝ)| * ‖Matrix.toEuclideanLin M v‖ ^ 2) ≤
    ENNReal.ofReal (‖v‖ ^ 2) * ENNReal.ofReal (|(k : ℝ)| * matrixFrobSq M)
  rw [← ENNReal.ofReal_mul (sq_nonneg ‖v‖)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ |(k : ℝ)| * (matrixFrobSq M * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (matrix_vector_norm_sq_le_frob M v) (abs_nonneg _)
    _ = _ := by ring

theorem boundaryDSq_matrix_unit_column_le (A : ℝ → CotangentMatrix n)
    (v : EuclideanSpace ℂ (CotangentIndex n)) (hv : ‖v‖ ≤ 1)
    (hA : ∀ i j, Continuous (fun θ => A θ i j)) :
    boundaryDSq (fun θ => A θ *ᵥ WithLp.ofLp v) ≤ matrixDSq A := by
  have hs : ‖v‖ ^ 2 ≤ (1 : ℝ) := by nlinarith [norm_nonneg v]
  have hw : ENNReal.ofReal (‖v‖ ^ 2) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs
  exact (boundaryDSq_matrix_constant_column_le A v hA).trans
    (by simpa only [one_mul] using mul_le_mul hw (le_refl (matrixDSq A)) bot_le bot_le)

theorem closedDisc_matrix_column_holomorphic (A : ℂ → CotangentMatrix n)
    (hA : ∀ i j, ContDiffOn ℂ ∞ (fun z => A z i j) (Metric.closedBall (0 : ℂ) 1))
    (v : EuclideanSpace ℂ (CotangentIndex n)) :
    HolomorphicColumn (fun z => A z *ᵥ WithLp.ofLp v) := by
  intro i
  change ContDiffOn ℂ ∞ (fun z => ∑ j, A z i j * v j) (Metric.closedBall (0 : ℂ) 1)
  exact ContDiffOn.sum fun j _ => (hA i j).mul contDiffOn_const

theorem closedDisc_matrix_unit_column_sup (A : ℂ → CotangentMatrix n) {L : ℝ}
    (hL : 0 ≤ L) (hA : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (A z) ≤ L)
    (v : EuclideanSpace ℂ (CotangentIndex n)) (hv : ‖v‖ ≤ 1) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ∑ i, ‖(A z *ᵥ WithLp.ofLp v) i‖ ^ 2 ≤ L ^ 2 := by
  intro z hz
  have hn : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (A z) v‖ ≤ L := by
    calc
      _ ≤ rectOpNorm (A z) * ‖v‖ := (Matrix.toEuclideanCLM (𝕜 := ℂ) (A z)).le_opNorm v
      _ ≤ L * 1 := mul_le_mul (hA z hz) hv (norm_nonneg v) hL
      _ = L := mul_one L
  have hs := (sq_le_sq₀ (norm_nonneg _) hL).2 hn
  simpa only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM] using hs

end Yau.Blueprint.V04Proof
