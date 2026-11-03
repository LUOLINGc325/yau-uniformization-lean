import Yau.Proofs.V04FactorUniqueness
import Yau.Proofs.V03Fourier

/-! Exact transport of the inverse operator norm and the original Fourier
seminorm to every given spectral factor. Infinite seminorms remain ENNReal. -/

open scoped Matrix ComplexOrder Topology ContDiff
open Filter
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem matrixFrobSq_mul_unitaryAdj (A U : CotangentMatrix n) (hU : Uᴴ * U = 1) :
    matrixFrobSq (A * Uᴴ) = matrixFrobSq A := by
  rw [← cotangentMatrixHS_norm_sq, ← cotangentMatrixHS_norm_sq,
    cotangentMatrixHS_norm_sq_trace, cotangentMatrixHS_norm_sq_trace]
  calc
    _ = (Matrix.trace (U * (Aᴴ * A) * Uᴴ)).re := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]

theorem rectOpNorm_mul_unitaryAdj (A U : CotangentMatrix n) (hU : Uᴴ * U = 1) :
    rectOpNorm (A * Uᴴ) = rectOpNorm A := by
  let φ := Matrix.toEuclideanCLM (n := CotangentIndex n) (𝕜 := ℂ)
  have hu : U ∈ unitary (CotangentMatrix n) := Matrix.mem_unitaryGroup_iff'.mpr hU
  have hs : star U ∈ unitary (CotangentMatrix n) := by
    constructor
    · simpa only [star_star] using hu.2
    · simpa only [star_star] using hu.1
  change ‖φ (A * star U)‖ = ‖φ A‖
  rw [map_mul]
  exact CStarRing.norm_mul_mem_unitary (φ A) (Unitary.map_mem φ hs)

theorem circleFourier_finite_sum {ι : Type*} (s : Finset ι) (u : ι → ℝ → ℂ)
    (hu : ∀ i, Continuous (u i)) (k : ℤ) :
    circleFourier (fun θ => ∑ i ∈ s, u i θ) k = ∑ i ∈ s, circleFourier (u i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [circleFourier]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [circleFourier_add (hu i) (continuous_finsetSum _ (fun j _ => hu j)), ih]

theorem circleFourier_mul_const (u : ℝ → ℂ) (c : ℂ) (k : ℤ) :
    circleFourier (fun θ => u θ * c) k = circleFourier u k * c := by
  simpa only [mul_comm] using circleFourier_const_mul u c k

theorem circleFourier_matrix_mul_const (A : ℝ → CotangentMatrix n) (U : CotangentMatrix n)
    (hA : ∀ i j, Continuous (fun θ => A θ i j)) (k : ℤ) :
    (fun i j => circleFourier (fun θ => (A θ * U) i j) k) =
      (show CotangentMatrix n from fun i j => circleFourier (fun θ => A θ i j) k) * U := by
  ext i j
  simp only [Matrix.mul_apply]
  rw [circleFourier_finite_sum Finset.univ (fun l θ => A θ i l * U l j)
    (fun l => (hA i l).mul continuous_const)]
  exact Finset.sum_congr rfl (fun l _ => circleFourier_mul_const _ _ k)

theorem matrixDSq_eq_tsum_frob_fourier (A : ℝ → CotangentMatrix n) :
    matrixDSq A = ∑' k : ℤ, ENNReal.ofReal (|(k : ℝ)| *
      matrixFrobSq (fun i j => circleFourier (fun θ => A θ i j) k)) := by
  calc
    matrixDSq A = ∑' p : CotangentIndex n × CotangentIndex n, ∑' k : ℤ,
        ENNReal.ofReal (|(k : ℝ)| * ‖circleFourier (fun θ => A θ p.1 p.2) k‖ ^ 2) := by
      rw [matrixDSq, boundaryDSq, tsum_fintype]
      simp only [Int.cast_abs]
    _ = ∑' k : ℤ, ∑' p : CotangentIndex n × CotangentIndex n,
        ENNReal.ofReal (|(k : ℝ)| * ‖circleFourier (fun θ => A θ p.1 p.2) k‖ ^ 2) :=
      ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)]
      congr 1
      simp only [matrixFrobSq, Fintype.sum_prod_type, Finset.mul_sum]

theorem matrixDSq_mul_unitaryAdj (A : ℝ → CotangentMatrix n) (U : CotangentMatrix n)
    (hA : ∀ i j, Continuous (fun θ => A θ i j)) (hU : Uᴴ * U = 1) :
    matrixDSq (fun θ => A θ * Uᴴ) = matrixDSq A := by
  rw [matrixDSq_eq_tsum_frob_fourier, matrixDSq_eq_tsum_frob_fourier]
  apply tsum_congr
  intro k
  rw [circleFourier_matrix_mul_const A Uᴴ hA k, matrixFrobSq_mul_unitaryAdj _ U hU]

theorem spectralFactorFor_inverse_norm_seminorm_eq {d : VariationData X q} {j a : ℕ} {δ : ℝ}
    {F : VariationDisc X} {E H Hinv K Kinv : ℂ → CotangentMatrix n}
    (hH : SpectralFactorFor d j a δ F E H Hinv)
    (hK : SpectralFactorFor d j a δ F E K Kinv) :
    (∀ z ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (Hinv z) = rectOpNorm (Kinv z)) ∧
      matrixDSq (fun θ => Hinv (circlePoint θ)) =
        matrixDSq (fun θ => Kinv (circlePoint θ)) := by
  obtain ⟨U, hU, h⟩ := spectralFactorFor_unitary_unique hH hK
  have hcircle (θ : ℝ) : circlePoint θ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp [Metric.mem_closedBall, dist_zero_right, circlePoint, Complex.norm_exp]
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [(h z hz).2]
    exact rectOpNorm_mul_unitaryAdj _ U hU
  · have htrace : (fun θ => Hinv (circlePoint θ)) =
        (fun θ => Kinv (circlePoint θ) * Uᴴ) := funext fun θ => (h _ (hcircle θ)).2
    rw [htrace]
    apply matrixDSq_mul_unitaryAdj _ U _ hU
    intro i l
    exact (hK.1 i l).2.continuousOn.comp_continuous
      (by unfold circlePoint; fun_prop : Continuous circlePoint) hcircle

theorem spectralFactorFor_transport_inverse_estimates {d : VariationData X q} {j a : ℕ} {δ C : ℝ}
    {F : VariationDisc X} {E H Hinv K Kinv : ℂ → CotangentMatrix n}
    (hH : SpectralFactorFor d j a δ F E H Hinv)
    (hK : SpectralFactorFor d j a δ F E K Kinv)
    (hKnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (Kinv z) ≤ (Real.sqrt δ)⁻¹)
    (hKsemi : matrixDSq (fun θ => Kinv (circlePoint θ)) ≤
      ENNReal.ofReal C * (1 + variationEnergy d j F)) :
    (∀ z ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (Hinv z) ≤ (Real.sqrt δ)⁻¹) ∧
      matrixDSq (fun θ => Hinv (circlePoint θ)) ≤
        ENNReal.ofReal C * (1 + variationEnergy d j F) := by
  obtain ⟨hnorm, hsemi⟩ := spectralFactorFor_inverse_norm_seminorm_eq hH hK
  exact ⟨fun z hz => (hnorm z hz).trans_le (hKnorm z hz), hsemi.trans_le hKsemi⟩

end Yau.Blueprint.V04Proof
