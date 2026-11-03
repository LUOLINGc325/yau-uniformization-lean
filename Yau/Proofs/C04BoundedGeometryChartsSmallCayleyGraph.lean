import Yau.Proofs.C04BoundedGeometryChartsUniformCayleyJets
import Yau.Proofs.C04FiniteDilation
import Yau.LeafProofs.L21Normalization

/-! One uniform finite dilation gives the actual integrable small Cayley graph. -/
noncomputable section
open Set
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem exists_uniform_small_coframe_graph (n : ℕ) (R : ℝ) (hR : 0 < R)
    (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) (q : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ d ≤ R / 4 ∧
      ∀ A : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n,
        ContDiff ℝ ∞ A → A 0 = ContinuousLinearMap.id ℝ (ComplexVector n) →
        (∀ m x, x ∈ Metric.closedBall (0 : ComplexVector n) R → ‖iteratedFDeriv ℝ m A x‖ ≤ B m) →
        (∀ x ∈ Metric.ball (0 : ComplexVector n) R, ∀ v,
          coframeComplexModel n (A x) (coframeComplexModel n (A x) v) = -v) →
        (∀ x ∈ Metric.ball (0 : ComplexVector n) R, ∀ v w,
          Yau.LeafCandidates.nijenhuis (fun y => coframeComplexModel n (A y)) x v w = 0) →
        (∀ x ∈ Metric.ball (0 : ComplexVector n) 2,
          (coframeComplexModel n (A (d • x)) + stdComplex n).IsInvertible) ∧
        MatrixSmoothOn (fun y => coframeCayleyGraphModel n (A (d • y))) (Metric.ball 0 2) ∧
        CommutesOn (fun y => coframeCayleyGraphModel n (A (d • y))) (Metric.ball 0 2) ∧
        JetBound q eta (fun y => coframeCayleyGraphModel n (A (d • y))) (Metric.ball 0 2) := by
  obtain ⟨s, hs, hsR, C, hC, hfamily⟩ := exists_uniform_coframe_cayley_jet_bounds n R hR B hB
  obtain ⟨d, hd, hd1, hds, hdsmall⟩ := C04Aux.uniform_finite_dilation_le
    (E := ComplexVector n) (F := Matrix (Fin n) (Fin n) ℂ) hs heta q C hC
  refine ⟨d, hd, hd1, hds.trans (by gcongr), ?_⟩
  intro A hA hA0 hjet hJ2 hN
  obtain ⟨hInv, hG, hGjet⟩ := hfamily A hA hA0 hjet
  have hdx (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) 2) :
      d • x ∈ Metric.ball (0 : ComplexVector n) s := by
    have hxn : ‖x‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    nlinarith
  have hdxR (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) 2) :
      d • x ∈ Metric.ball (0 : ComplexVector n) R := Metric.ball_subset_ball hsR (hdx x hx)
  let J := fun y => coframeComplexModel n (A y)
  let Jd := fun y => J (d • y)
  have hJat (y : ComplexVector n) (hy : y ∈ Metric.ball (0 : ComplexVector n) s) :
      ContDiffAt ℝ ∞ J y := by
    simpa only [J, Function.comp_def] using
      (coframeComplexModel_smoothAt (A y) (hInv y (Metric.ball_subset_closedBall hy)).1).comp y hA.contDiffAt
  have hJd : ContDiffOn ℝ ∞ Jd (Metric.ball (0 : ComplexVector n) 2) := by
    intro x hx
    exact ((hJat _ (hdx x hx)).comp x
      ((contDiff_id.const_smul d).contDiffAt)).contDiffWithinAt
  have hJd2 : ∀ x ∈ Metric.ball (0 : ComplexVector n) 2, ∀ v, Jd x (Jd x v) = -v := by
    intro x hx v
    exact hJ2 _ (hdxR x hx) v
  have hNd : ∀ x ∈ Metric.ball (0 : ComplexVector n) 2, ∀ v w,
      Yau.LeafCandidates.nijenhuis Jd x v w = 0 := by
    intro x hx v w
    have H := nijenhuis_rescaleStructure (0 : ComplexVector n)
      (ContinuousLinearEquiv.refl ℝ (ComplexVector n)) d
      (J := J) (z := x) (by
        simpa only [rescalePoint, ContinuousLinearEquiv.refl_symm,
          ContinuousLinearEquiv.refl_apply, zero_add] using (hJat _ (hdx x hx)).differentiableAt (by simp)) v w
    have heq : rescaleStructure (0 : ComplexVector n)
        (ContinuousLinearEquiv.refl ℝ (ComplexVector n)) d J = Jd := by
      funext y
      apply ContinuousLinearMap.ext
      intro v
      simp only [rescaleStructure_apply, rescalePoint, ContinuousLinearEquiv.refl_symm,
        ContinuousLinearEquiv.refl_apply, zero_add]
      rfl
    rw [heq] at H
    have hNz : Yau.LeafCandidates.nijenhuis J (d • x) v w = 0 := hN _ (hdxR x hx) v w
    simpa only [rescalePoint, ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.refl_apply,
      zero_add, hNz, smul_zero] using H
  have hId : ∀ x ∈ Metric.ball (0 : ComplexVector n) 2, (Jd x + stdComplex n).IsInvertible :=
    fun x hx => (hInv _ (Metric.ball_subset_closedBall (hdx x hx))).2
  have hwhole : ContDiffOn ℝ ∞ (fun y => coframeCayleyGraphModel n (A (d • y))) (Metric.ball 0 2) :=
    hG.comp (contDiff_id.const_smul d).contDiffOn (fun x hx => hdx x hx)
  have hsmall := hdsmall (fun y => coframeCayleyGraphModel n (A y)) hG
    (by rw [hA0, coframeCayleyGraphModel_id]) (fun j hj x hx => hGjet j x hx)
  refine ⟨hId, cayley_graph_matrix_smooth Metric.isOpen_ball hJd hId,
    cayley_graph_commutes Metric.isOpen_ball hJd hJd2 hNd hId, ?_⟩
  intro j hj x hx i k
  exact (norm_iteratedFDeriv_matrixEntry_le
    (hwhole.contDiffAt (Metric.isOpen_ball.mem_nhds hx)) j i k).trans (hsmall j hj x hx)

end Yau.Proofs.C04ChartsAux
