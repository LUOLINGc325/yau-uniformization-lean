import Yau.Proofs.V02CenterForward
import Yau.Proofs.V02QuadraticBounds
import Yau.Proofs.V03PartialWirtinger

/-! The actual smooth test has a bounded spatial Hessian on the fixed
center cylinder, and every supplied normalized frame has the same bound. -/

open scoped Topology ContDiff Manifold Matrix
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def testChartHessian (d : VariationData X q) (p : CotangentCoord n × ℝ) : CotangentMatrix n :=
  leviMatrix (fun z => d.test (cotangentChartInv d.chart z) p.2) p.1 cotangentDir

theorem testChartHessian_entry_continuousOn
    {d : VariationData X q} (hc : StrictEnvelopeContact d) (a b : CotangentIndex n) :
    ContinuousOn (fun p => testChartHessian d p a b) (centerCylinder d) := by
  obtain ⟨V, hV, hCV, _, hs⟩ := hc.2.2.2.2.2.2
  intro p hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV p (hCV hp)
  have hprod : ball p.1 ε ×ˢ ball p.2 ε ⊆ V := by
    intro y hy
    apply hball
    rw [mem_ball, Prod.dist_eq]
    exact max_lt (mem_ball.mp hy.1) (mem_ball.mp hy.2)
  have hentry := V03Proof.leviMatrix_parameter_contDiffOn isOpen_ball
    (isOpen_ball.uniqueDiffOn.prod isOpen_ball.uniqueDiffOn) (hs.mono hprod) cotangentDir a b
  have hp' : p ∈ ball p.1 ε ×ˢ ball p.2 ε := ⟨mem_ball_self hε, mem_ball_self hε⟩
  exact ((hentry.contDiffAt ((isOpen_ball.prod isOpen_ball).mem_nhds hp')).continuousAt).continuousWithinAt

theorem testChartHessian_uniform_norm {d : VariationData X q} (hc : StrictEnvelopeContact d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ centerCylinder d, rectOpNorm (testChartHessian d p) ≤ M := by
  have hH : ContinuousOn (testChartHessian d) (centerCylinder d) :=
    continuousOn_pi.mpr (fun a => continuousOn_pi.mpr (fun b =>
      testChartHessian_entry_continuousOn hc a b))
  have hn := rectOpNorm_continuous.comp_continuousOn hH
  obtain ⟨M, hM⟩ := hc.1.bddAbove_image hn
  exact ⟨max M 0, le_max_right _ _, fun p hp =>
    (hM ⟨p, hp, rfl⟩).trans (le_max_left _ _)⟩

theorem centerTestHessian_in_fixed_chart
    {d : VariationData X q} (hc : StrictEnvelopeContact d)
    {F : VariationDisc X} (hcenter : InCotangentTimeChart d.chart (F.f 0) F.s (centerCylinder d))
    (E : ℂ → CotangentMatrix n) :
    centerTestHessian d F E = (frameInChart d.chart F.f E 0)ᴴ *
      testChartHessian d (cotangentChart d.chart (F.f 0), F.s) * frameInChart d.chart F.f E 0 := by
  obtain ⟨V, hV, hCV, _, hs⟩ := hc.2.2.2.2.2.2
  have hslice : ContDiffAt ℝ 2 (fun z => d.test (cotangentChartInv d.chart z) F.s)
      (cotangentChart d.chart (F.f 0)) :=
    (((hs.contDiffAt (hV.mem_nhds (hCV hcenter.2))).comp
      (cotangentChart d.chart (F.f 0)) (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp))
  rw [centerTestHessian, V03Proof.spatialHessian_in_fixed_chart
    (fun y => d.test y F.s) d.chart hcenter.1 hslice]
  simp only [frameInChart, testChartHessian, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem centerTestHessian_uniform_norm
    {d : VariationData X q} (hd : VariationSetup d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      rectOpNorm (centerTestHessian d F E) ≤ C := by
  obtain ⟨M, hM, hH⟩ := testChartHessian_uniform_norm hd.2.2.2.2.2.2.2.1
  obtain ⟨B, hB, hframe⟩ := centerFrame_forward_bound hd
  refine ⟨B ^ 2 * M, mul_nonneg (sq_nonneg _) hM, fun j F E hF hE => ?_⟩
  rw [centerTestHessian_in_fixed_chart hd.2.2.2.2.2.2.2.1 hF.2.2.2.2.2.1]
  have hf := hframe j F E hF hE
  have hsq : rectOpNorm (frameInChart d.chart F.f E 0) ^ 2 ≤ B ^ 2 := by
    have hh := mul_self_le_mul_self (V03Proof.rectOpNorm_nonneg _) hf
    simpa only [← sq] using hh
  exact (rectOpNorm_sandwich_le _ _).trans (mul_le_mul hsq
    (hH _ hF.2.2.2.2.2.1.2) (norm_nonneg _) (sq_nonneg _))

theorem centerTest_quadratic_uniform_bound
    {d : VariationData X q} (hd : VariationSetup d) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      (∀ ζ ∈ closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      |quadValue (centerTestHessian d F E) (l 0)| ≤ C := by
  obtain ⟨M, hM, hbound⟩ := centerTestHessian_uniform_norm hd
  refine ⟨M * L ^ 2, mul_nonneg hM (sq_nonneg _), fun j F E l hF hE hl => ?_⟩
  exact (abs_quadValue_le_rectOpNorm _ _).trans
    (mul_le_mul (hbound j F E hF hE) (hl 0 (by simp))
      (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hM)

end Yau.Blueprint.V02Proof
