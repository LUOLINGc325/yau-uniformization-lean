import Yau.Proofs.V04HilbertClipping
import Mathlib.Analysis.Complex.AbsMax

/-! A matrix and its holomorphic inverse with unitary boundary values are
constant on the closed disc. All norms below are Euclidean vector or entry
Hilbert norms; the empty index type requires no unit vector. -/

open scoped Matrix ComplexOrder InnerProductSpace Topology ContDiff
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem cotangentMatrixHS_injective : Function.Injective (cotangentMatrixHS (n := n)) := by
  intro A B h
  ext i j
  exact congrArg (fun v : EuclideanSpace ℂ (CotangentIndex n × CotangentIndex n) => v (i, j)) h

theorem cotangentMatrixHS_norm_sq_trace (A : CotangentMatrix n) :
    ‖cotangentMatrixHS A‖ ^ 2 = (Matrix.trace (Aᴴ * A)).re := by
  have hinner : inner ℝ (cotangentMatrixHS A) (cotangentMatrixHS A) =
      (Matrix.trace (Aᴴ * A)).re := by
    rw [PiLp.inner_apply]
    simp only [cotangentMatrixHS, PiLp.toLp_apply, real_inner_eq_re_inner ℂ,
      RCLike.re_eq_complex_re]
    rw [← Complex.re_sum]
    apply congrArg Complex.re
    simp only [RCLike.inner_apply', Fintype.sum_prod_type,
      Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp only [← Complex.star_def]
    exact Finset.sum_comm
  simpa only [real_inner_self_eq_norm_sq] using hinner

theorem euclidean_norm_map_of_gram_one (A : CotangentMatrix n) (hA : Aᴴ * A = 1)
    (v : EuclideanSpace ℂ (CotangentIndex n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖ = ‖v‖ := by
  let φ := Matrix.toEuclideanCLM (n := CotangentIndex n) (𝕜 := ℂ)
  have hstar : star A * A = 1 := hA
  have hφ : star (φ A) * φ A = 1 := by
    rw [← map_star, ← map_mul, hstar, map_one]
  exact (φ A).norm_map_iff_adjoint_comp_self.mpr hφ v

theorem gram_one_of_euclidean_norm_map (A : CotangentMatrix n)
    (hA : ∀ v : EuclideanSpace ℂ (CotangentIndex n),
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A v‖ = ‖v‖) : Aᴴ * A = 1 := by
  let φ := Matrix.toEuclideanCLM (n := CotangentIndex n) (𝕜 := ℂ)
  have hφ : star (φ A) * φ A = 1 :=
    (φ A).norm_map_iff_adjoint_comp_self.mp hA
  have heq : φ (star A * A) = φ 1 := by
    simpa only [map_mul, map_star, map_one] using hφ
  exact φ.injective heq

theorem closedDisc_matrix_contraction (Q : ℂ → CotangentMatrix n)
    (hQ : ∀ i j, ContDiffOn ℂ ∞ (fun z => Q z i j) (Metric.closedBall (0 : ℂ) 1))
    (hboundary : ∀ θ, (Q (circlePoint θ))ᴴ * Q (circlePoint θ) = 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1)
    (v : EuclideanSpace ℂ (CotangentIndex n)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Q z) v‖ ≤ ‖v‖ := by
  let F : ℂ → EuclideanSpace ℂ (CotangentIndex n) :=
    fun ζ => Matrix.toEuclideanCLM (𝕜 := ℂ) (Q ζ) v
  have hF : ContDiffOn ℂ ∞ F (Metric.closedBall (0 : ℂ) 1) := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    change ContDiffOn ℂ ∞ (fun ζ => ∑ j, Q ζ i j * v j) (Metric.closedBall (0 : ℂ) 1)
    exact ContDiffOn.sum fun j _ => (hQ i j).mul contDiffOn_const
  have hd : DiffContOnCl ℂ F (Metric.ball 0 1) :=
    ((hF.differentiableOn (by simp)).mono Metric.closure_ball_subset_closedBall).diffContOnCl
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_ ?_
  · intro w hw
    have hwn : ‖w‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using Metric.frontier_ball_subset_sphere hw
    have hc : circlePoint (Complex.arg w) = w := by
      simpa only [circlePoint, hwn, Complex.ofReal_one, one_mul] using
        Complex.norm_mul_exp_arg_mul_I w
    rw [← hc]
    exact (euclidean_norm_map_of_gram_one _ (hboundary _) v).le
  · simpa only [closure_ball _ one_ne_zero] using hz

theorem closedDisc_matrix_inverse_unitary_constant (Q R : ℂ → CotangentMatrix n)
    (hQ : ∀ i j, ContDiffOn ℂ ∞ (fun z => Q z i j) (Metric.closedBall (0 : ℂ) 1))
    (hR : ∀ i j, ContDiffOn ℂ ∞ (fun z => R z i j) (Metric.closedBall (0 : ℂ) 1))
    (hRQ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, R z * Q z = 1)
    (hQboundary : ∀ θ, (Q (circlePoint θ))ᴴ * Q (circlePoint θ) = 1)
    (hRboundary : ∀ θ, (R (circlePoint θ))ᴴ * R (circlePoint θ) = 1) :
    (Q 0)ᴴ * Q 0 = 1 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Q z = Q 0 := by
  let φ := Matrix.toEuclideanCLM (n := CotangentIndex n) (𝕜 := ℂ)
  have hgram : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, (Q z)ᴴ * Q z = 1 := by
    intro z hz
    apply gram_one_of_euclidean_norm_map
    intro v
    have hdown := closedDisc_matrix_contraction Q hQ hQboundary hz v
    have hup := closedDisc_matrix_contraction R hR hRboundary hz (φ (Q z) v)
    have hid : φ (R z) (φ (Q z) v) = v := by
      calc
        _ = (φ (R z) * φ (Q z)) v := rfl
        _ = φ (R z * Q z) v := by rw [map_mul]
        _ = v := by rw [hRQ z hz, map_one]; rfl
    change ‖φ (R z) (φ (Q z) v)‖ ≤ ‖φ (Q z) v‖ at hup
    rw [hid] at hup
    exact le_antisymm hdown hup
  have hzero : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by simp
  refine ⟨hgram 0 hzero, ?_⟩
  let F : ℂ → EuclideanSpace ℂ (CotangentIndex n × CotangentIndex n) :=
    fun z => cotangentMatrixHS (Q z)
  have hF : ContDiffOn ℂ ∞ F (Metric.closedBall (0 : ℂ) 1) := by
    apply (contDiffOn_piLp 2).mpr
    intro p
    exact hQ p.1 p.2
  have hd : DiffContOnCl ℂ F (Metric.ball 0 1) :=
    ((hF.differentiableOn (by simp)).mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ‖F z‖ = ‖F 0‖ := by
    intro z hz
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    dsimp [F]
    rw [cotangentMatrixHS_norm_sq_trace, cotangentMatrixHS_norm_sq_trace,
      hgram z hz, hgram 0 hzero]
  have hmax : IsMaxOn (norm ∘ F) (Metric.ball (0 : ℂ) 1) 0 :=
    fun z hz => (hnorm z (Metric.ball_subset_closedBall hz)).le
  have hconst := Complex.eqOn_closedBall_of_isMaxOn_norm hd hmax
  intro z hz
  apply cotangentMatrixHS_injective
  exact hconst hz

end Yau.Blueprint.V04Proof
