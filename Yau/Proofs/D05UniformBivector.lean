import Yau.Proofs.D05FrameBivector
import Yau.Proofs.D05FrobeniusAlgebra
import Mathlib.Analysis.Complex.AbsMax

/-! A compact boundary set controls the bivector of every normalized
closed-disc frame, independently of the selected frame and its construction. -/

open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

theorem ambientBivector_compact_bound {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentHolomorphic G)
    {K : Set (CotangentPoint M)} (hK : CotangentCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ y ∈ K, matrixFrobSq (ambientBivector G y) ≤ C ^ 2 := by
  classical
  obtain ⟨b, x, S, hS, hKeq⟩ := hK
  have hb : ∀ i : Fin b, ∃ B : ℝ, ∀ z ∈ S i,
      ‖(WithLp.toLp 2 (fun p : Fin q × Fin q =>
        ambientBivector G (cotangentChartInv (x i) z) p.1 p.2) :
          EuclideanSpace ℂ (Fin q × Fin q))‖ ≤ B := by
    intro i
    let F : CotangentCoord n → EuclideanSpace ℂ (Fin q × Fin q) :=
      fun z => WithLp.toLp 2 (fun p => ambientBivector G (cotangentChartInv (x i) z) p.1 p.2)
    have hF : ContinuousOn F (S i) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin q × Fin q => ℂ)).comp_continuousOn
      apply continuousOn_pi.mpr
      intro p
      exact (ambientBivector_chart_contDiffOn hG (x i) p.1 p.2).continuousOn.mono (hS i).2
    obtain ⟨B, hB⟩ := (hS i).1.bddAbove_image hF.norm
    exact ⟨B, fun z hz => hB ⟨z, hz, rfl⟩⟩
  choose B hB using hb
  let C : ℝ := 1 + ∑ i, max 0 (B i)
  have hsum : 0 ≤ ∑ i, max 0 (B i) := Finset.sum_nonneg fun i _ => le_max_left _ _
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro y hy
  rw [hKeq] at hy
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  obtain ⟨z, hz, rfl⟩ := hi
  have hBi : B i ≤ C := by
    have hle : max 0 (B i) ≤ ∑ j, max 0 (B j) :=
      Finset.single_le_sum (fun j _ => le_max_left _ _) (Finset.mem_univ i)
    dsimp only [C]
    linarith [le_max_right 0 (B i)]
  rw [matrixFrobSq_eq_flatten_norm_sq]
  exact (sq_le_sq₀ (norm_nonneg _) hC.le).mpr ((hB i z hz).trans hBi)

theorem normalizedFrame_uniform_bivector {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (K : Set (CotangentPoint M)) (hK : CotangentCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ f E, NormalizedDiscFrame G f E →
      (∀ θ, f (circlePoint θ) ∈ K) → ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        matrixFrobSq (frameBivector (E z)) ≤ C ^ 2 := by
  obtain ⟨C, hC, hCB⟩ := ambientBivector_compact_bound hG.1 hK
  refine ⟨C, hC, ?_⟩
  intro f E hE hboundary
  let F : ℂ → EuclideanSpace ℂ (CotangentIndex n × CotangentIndex n) :=
    fun z => WithLp.toLp 2 (fun p => frameBivector (E z) p.1 p.2)
  have hF : ContDiffOn ℂ ∞ F (Metric.closedBall (0 : ℂ) 1) := by
    apply (contDiffOn_piLp 2).mpr
    intro p
    exact frameBivector_entry_contDiffOn hE.1 p.1 p.2
  have hcircle : ∀ θ, ‖F (circlePoint θ)‖ ≤ C := by
    intro θ
    have heq := matrixFrobSq_rectangular_isometry
      (ambientFrame G f E (circlePoint θ)) (hE.2.1 θ) (frameBivector (E (circlePoint θ)))
    rw [← ambientBivector_eq_frame_pushforward G f hE.1 (circlePoint_mem_closedBall θ)] at heq
    have hb : matrixFrobSq (frameBivector (E (circlePoint θ))) ≤ C ^ 2 := by
      rw [← heq]
      exact hCB _ (hboundary θ)
    rw [matrixFrobSq_eq_flatten_norm_sq] at hb
    exact (sq_le_sq₀ (norm_nonneg _) hC.le).mp hb
  have hd : DiffContOnCl ℂ F (Metric.ball 0 1) :=
    ((hF.differentiableOn (by simp)).mono Metric.closure_ball_subset_closedBall).diffContOnCl
  intro z hz
  have hn : ‖F z‖ ≤ C := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd ?_ ?_
    · intro w hw
      have hwn : ‖w‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using Metric.frontier_ball_subset_sphere hw
      have hc : circlePoint (Complex.arg w) = w := by
        simpa only [circlePoint, hwn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I w
      rw [← hc]
      exact hcircle _
    · simpa only [closure_ball _ one_ne_zero] using hz
  rw [matrixFrobSq_eq_flatten_norm_sq]
  exact (sq_le_sq₀ (norm_nonneg _) hC.le).mpr hn

end Yau.Blueprint.D05Proof
