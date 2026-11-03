import Yau.Proofs.C04BoundedGeometryChartsSmallCayleyGraph
import Yau.LeafProofs.L21WeightedDomains
import Yau.LeafProofs.L21SmallColumnCoordinates
import Yau.LeafProofs.L21CoordinateChart
import Yau.LeafProofs.L21MatrixBounds

/-! One uniformly normalized coordinate function is chosen before any higher-order estimate. -/
noncomputable section
open MeasureTheory Set
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem coordinate_function_norm_le {n : ℕ} (F : ComplexVector n → ComplexVector n)
    (hF : ContDiff ℝ ∞ F) (hF0 : F 0 = 0)
    (hclose : ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
      ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ))
    {x : ComplexVector n} (hx : x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) :
    ‖F x‖ ≤ (5 / 4 : ℝ) * ‖x‖ := by
  have hderiv : ∀ y ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ‖fderiv ℝ F y‖ ≤ (5 / 4 : ℝ) := by
    intro y hy
    have ht := norm_add_le (fderiv ℝ F y - ContinuousLinearMap.id ℝ (ComplexVector n))
      (ContinuousLinearMap.id ℝ (ComplexVector n))
    rw [sub_add_cancel] at ht
    have hi := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ComplexVector n)
    linarith [hclose y hy]
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy => hF.differentiable (by simp) y)
    hderiv (convex_ball (0 : ComplexVector n) (1 / 2 : ℝ))
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)) hx
  simpa only [hF0, sub_zero] using H

theorem exists_uniform_coframe_coordinate_function (n : ℕ) (R : ℝ) (hR : 0 < R)
    (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ d ≤ R / 4 ∧
      ∀ A : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n,
        ContDiff ℝ ∞ A → A 0 = ContinuousLinearMap.id ℝ (ComplexVector n) →
        (∀ m x, x ∈ Metric.closedBall (0 : ComplexVector n) R → ‖iteratedFDeriv ℝ m A x‖ ≤ B m) →
        (∀ x ∈ Metric.ball (0 : ComplexVector n) R, ∀ v,
          coframeComplexModel n (A x) (coframeComplexModel n (A x) v) = -v) →
        (∀ x ∈ Metric.ball (0 : ComplexVector n) R, ∀ v w,
          Yau.LeafCandidates.nijenhuis (fun y => coframeComplexModel n (A y)) x v w = 0) →
        ∃ F : ComplexVector n → ComplexVector n, ContDiff ℝ ∞ F ∧ F 0 = 0 ∧
          (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
            ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ)) ∧
          (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ v,
            fderiv ℝ F x (coframeComplexModel n (A (d • x)) v) = Complex.I • fderiv ℝ F x v) ∧
          ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ‖F x‖ ≤ 1 := by
  obtain ⟨eps, W, heps, hW, hSolve⟩ := weightedDomains_exists_small_column_solutions n
  obtain ⟨delta, hdelta, hCoordinates⟩ := exists_small_weighted_column_coordinates (n := n) W hW.le
  let eta := min 1 (min eps (min delta (1 / (2 * ((n : ℝ)^2 + 1)))))
  have heta : 0 < eta := lt_min zero_lt_one (lt_min heps (lt_min hdelta (by positivity)))
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hetae : eta ≤ eps := (min_le_right _ _).trans (min_le_left _ _)
  have hetad : eta ≤ delta := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hetan : eta ≤ 1 / (2 * ((n : ℝ)^2 + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨d, hd, hd1, hdR, hfamily⟩ := exists_uniform_small_coframe_graph n R hR B hB
    (realDimension n + 4) eta heta
  refine ⟨d, hd, hd1, hdR, ?_⟩
  intro A hA hA0 hjet hJ2 hN
  obtain ⟨hInv, hSmooth, hComm, hJet⟩ := hfamily A hA hA0 hjet hJ2 hN
  let G := fun y => coframeCayleyGraphModel n (A (d • y))
  let Jd := fun y => coframeComplexModel n (A (d • y))
  have hJetBound (s : ℕ) (hs : s ≤ realDimension n + 4) (b : ℝ) (hb : eta ≤ b) :
      JetBound s b G (Metric.ball 0 2) := fun k hk x hx i j => (hJet k (hk.trans hs) x hx i j).trans hb
  have hOp : ∀ x ∈ Metric.ball (0 : ComplexVector n) 2, Yau.LeafCandidates.matrixOpNorm (G x) ≤ 1 / 2 :=
    jetBound_small_matrixOpNorm (hJetBound _ le_rfl _ hetan)
  have h12 : Metric.ball (0 : ComplexVector n) 1 ⊆ Metric.ball 0 2 := Metric.ball_subset_ball (by norm_num)
  have hSolutions : ∀ k : Fin n, ∃ u : ComplexVector n → ℂ,
      MemLp u 2 (weightedBallMeasure n W) ∧ DbarWeakOn G u (fun x i => G x i k) (Metric.ball 0 1) ∧
        (∫ x, ‖u x‖^2 ∂weightedBallMeasure n W) ≤ ∑ j, ∫ x, ‖(rho x : ℂ)*G x j k‖^2 ∂weightedBallMeasure n W := by
    intro k
    obtain ⟨u, hu, hlocal, hweak, hmass⟩ := hSolve G hSmooth (hJetBound 1 (by omega) eps hetae)
      (hJetBound 2 (by omega) 1 heta1) hComm k
    exact ⟨u, hu, hweak, hmass⟩
  obtain ⟨F, hF, hD, hclose⟩ := hCoordinates G (fun i j => (hSmooth i j).mono h12)
    (fun x hx => hOp x (h12 hx)) (jetBound_mono_domain h12 (hJetBound _ (by omega) 1 heta1))
    (jetBound_mono_domain h12 (hJetBound _ (by omega) delta hetad)) hSolutions
  let H := fun x => F x - F 0
  have hH : ContDiff ℝ ∞ H := hF.sub contDiff_const
  have hH0 : H 0 = 0 := sub_self _
  have hHclose : ∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
      ‖fderiv ℝ H x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ) := by
    intro x hx
    simpa only [H, fderiv_sub_const] using hclose x hx
  refine ⟨H, hH, hH0, hHclose, ?_, ?_⟩
  · intro x hx v
    have hx2 : x ∈ Metric.ball (0 : ComplexVector n) 2 := Metric.ball_subset_ball (by norm_num) hx
    have hdx : d • x ∈ Metric.ball (0 : ComplexVector n) R := by
      have hn : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
      nlinarith
    have hh := vector_intertwines_of_dbarA_eq_zero Jd x (hJ2 _ hdx) (hInv x hx2)
      F (hF.differentiable (by simp) x) (hD x hx) v
    simpa only [H, fderiv_sub_const] using hh
  · intro x hx
    have hn : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact (coordinate_function_norm_le H hH hH0 hHclose hx).trans (by nlinarith)

end Yau.Proofs.C04ChartsAux
