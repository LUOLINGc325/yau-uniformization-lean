import Yau.Proofs.D05GaussDensity
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.AbsMax

/-! Boundary column orthonormality bounds the genuine Euclidean operator
norm throughout the closed disc, for arbitrary rectangular matrices. -/

open scoped Topology ContDiff Matrix
open Filter

noncomputable section
namespace Yau.Blueprint.D05Proof

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem norm_map_of_column_gram_one (U : Matrix κ ι ℂ) (hU : Uᴴ * U = 1)
    (v : EuclideanSpace ℂ ι) : ‖Matrix.toEuclideanLin U v‖ = ‖v‖ := by
  classical
  have hid : (Matrix.toEuclideanLin U).adjoint.comp (Matrix.toEuclideanLin U) = LinearMap.id := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [← Matrix.toLpLin_mul_same, hU, Matrix.toLpLin_one]
  have hv : (Matrix.toEuclideanLin U).adjoint (Matrix.toEuclideanLin U v) = v :=
    congrArg (fun L => L v) hid
  have hi : inner ℂ (Matrix.toEuclideanLin U v) (Matrix.toEuclideanLin U v) = inner ℂ v v := by
    rw [← LinearMap.adjoint_inner_right, hv]
  have hs : ‖Matrix.toEuclideanLin U v‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [inner_self_eq_norm_sq] using congrArg (fun w : ℂ => RCLike.re w) hi
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem matrix_closedDisc_norm_le_of_boundary {U : ℂ → Matrix κ ι ℂ}
    (hU : ∀ i j, ContDiffOn ℂ ∞ (fun z => U z i j) (Metric.closedBall (0 : ℂ) 1))
    (hboundary : ∀ θ : ℝ, (U (circlePoint θ))ᴴ * U (circlePoint θ) = 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) (v : EuclideanSpace ℂ ι) :
    ‖Matrix.toEuclideanLin (U z) v‖ ≤ ‖v‖ := by
  let F : ℂ → EuclideanSpace ℂ κ := fun w => Matrix.toEuclideanLin (U w) v
  have hF : ContDiffOn ℂ ∞ F (Metric.closedBall (0 : ℂ) 1) := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    change ContDiffOn ℂ ∞ (fun w => ∑ j, U w i j * v j) (Metric.closedBall (0 : ℂ) 1)
    exact ContDiffOn.sum fun j _ => (hU i j).mul contDiffOn_const
  have hd : DiffContOnCl ℂ F (Metric.ball 0 1) :=
    ((hF.differentiableOn (by simp)).mono Metric.closure_ball_subset_closedBall).diffContOnCl
  apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_ ?_
  · intro w hw
    have hwn : ‖w‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using Metric.frontier_ball_subset_sphere hw
    have hcircle : circlePoint (Complex.arg w) = w := by
      simpa only [circlePoint, hwn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I w
    change ‖Matrix.toEuclideanLin (U w) v‖ ≤ ‖v‖
    rw [← hcircle]
    exact (norm_map_of_column_gram_one _ (hboundary (Complex.arg w)) v).le
  · simpa only [closure_ball _ one_ne_zero] using hz

theorem rectOpNorm_le_one_of_boundary {U : ℂ → Matrix κ ι ℂ}
    (hU : ∀ i j, ContDiffOn ℂ ∞ (fun z => U z i j) (Metric.closedBall (0 : ℂ) 1))
    (hboundary : ∀ θ : ℝ, (U (circlePoint θ))ᴴ * U (circlePoint θ) = 1)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : rectOpNorm (U z) ≤ 1 := by
  classical
  unfold rectOpNorm
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [one_mul]
  change ‖Matrix.toEuclideanLin (U z) v‖ ≤ ‖v‖
  exact matrix_closedDisc_norm_le_of_boundary hU hboundary hz v

theorem normalizedFrame_of_boundary {n q : ℕ} {M : Yau.ComplexManifold n}
    {G : CotangentPoint M → Yau.ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ → CotangentPoint M} {E : ℂ → CotangentMatrix n} (hE : IsDiscFrame f E)
    (hboundary : ∀ θ : ℝ,
      (ambientFrame G f E (circlePoint θ))ᴴ * ambientFrame G f E (circlePoint θ) = 1) :
    NormalizedDiscFrame G f E := by
  refine ⟨hE, hboundary, ?_, normalizedFrame_gaussFourier hG hE hboundary⟩
  intro z hz
  exact rectOpNorm_le_one_of_boundary (V03Proof.ambientFrame_entry_contDiffOn hE hG.1)
    hboundary (Metric.ball_subset_closedBall hz)

end Yau.Blueprint.D05Proof
