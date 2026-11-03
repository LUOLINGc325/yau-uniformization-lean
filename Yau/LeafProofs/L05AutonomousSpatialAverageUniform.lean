import Yau.LeafProofs.L05AutonomousMollifierSpace

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- Actual positive spatial averages converge uniformly on a true buffer of a
uniformly continuous representative. The integrals are Bochner integrable by
the stated bound on the genuine kernel support. -/
theorem auto_spatial_average_uniform {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {K S : Set (Point n)} (hSK : S ⊆ K)
    (f : Point n → E) (hf : StronglyMeasurable f) (hUC : UniformContinuousOn f K)
    {C : ℝ} (hBound : ∀ p∈K, ‖f p‖ ≤ C)
    (eps : ℕ → ℝ) (heps : ∀ j, 0 < eps j) (hzero : Tendsto eps atTop (𝓝 0))
    (hBuffer : ∀ j, ∀ p∈S, ∀ q∈Metric.closedBall (0 : Space n) (eps j), (p.1-q,p.2)∈K) :
    (∀ j, ∀ p∈S, Integrable (fun q => f (p.1-q,p.2)) (autoMollifierMeasure n (eps j) (heps j))) ∧
      TendstoUniformlyOn
        (fun j p => ∫ q, f (p.1-q,p.2) ∂autoMollifierMeasure n (eps j) (heps j)) f atTop S := by
  have hInt (j : ℕ) (p : Point n) (hp : p∈S) :
      Integrable (fun q => f (p.1-q,p.2)) (autoMollifierMeasure n (eps j) (heps j)) := by
    let : IsProbabilityMeasure (autoMollifierMeasure n (eps j) (heps j)) :=
      autoMollifierMeasure_isProbability n (eps j) (heps j)
    apply Integrable.of_bound
      (hf.comp_measurable ((continuous_const.sub continuous_id).prodMk continuous_const).measurable).aestronglyMeasurable C
    filter_upwards [autoMollifierMeasure_closedBall_ae n (eps j) (heps j)] with q hq
    exact hBound _ (hBuffer j p hp q hq)
  refine ⟨hInt,?_⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eta heta
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC (eta/2) (half_pos heta)
  filter_upwards [hzero.eventually (gt_mem_nhds hdelta)] with j hj p hp
  let nu := autoMollifierMeasure n (eps j) (heps j)
  let : IsProbabilityMeasure nu := autoMollifierMeasure_isProbability n (eps j) (heps j)
  have hEq : (∫ q, f (p.1-q,p.2) ∂nu)-f p=
      ∫ q, (f (p.1-q,p.2)-f p) ∂nu := by
    rw [integral_sub (hInt j p hp) (integrable_const _),integral_const,probReal_univ,one_smul]
  have hNorm := norm_integral_le_of_norm_le_const (μ := nu)
    (f := fun q => f (p.1-q,p.2)-f p) (C := eta/2) (by
      filter_upwards [autoMollifierMeasure_closedBall_ae n (eps j) (heps j)] with q hq
      have hqn : ‖q‖ ≤ eps j := by simpa only [Metric.mem_closedBall,dist_zero_right] using hq
      have hDist : dist (p.1-q,p.2) p < delta := by
        rw [Prod.dist_eq,dist_self,max_eq_left dist_nonneg,dist_eq_norm,
          show p.1-q-p.1=-q by abel,norm_neg]
        exact hqn.trans_lt hj
      simpa only [dist_eq_norm] using (hclose _ (hBuffer j p hp q hq) p (hSK hp) hDist).le)
  rw [← hEq] at hNorm
  have hFinal : ‖(∫ q, f (p.1-q,p.2) ∂nu)-f p‖ < eta := by
    exact (by simpa only [probReal_univ,mul_one] using hNorm :
      ‖(∫ q, f (p.1-q,p.2) ∂nu)-f p‖ ≤ eta/2).trans_lt (half_lt_self heta)
  simpa only [dist_eq_norm,norm_sub_rev] using hFinal

end Yau.LeafProofs.L05AutonomousAux
