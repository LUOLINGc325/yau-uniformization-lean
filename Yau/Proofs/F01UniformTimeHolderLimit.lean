import spec.CHAIN.CONTRACTS
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! A common quantitative time modulus makes every Cauchy clock
sequence uniformly convergent in the spatial variable. Completeness
constructs the limit; no terminal representative is an input. -/
noncomputable section
open Set Filter Metric
open scoped Topology
namespace Yau.NodeProofs.F01Aux
variable {A F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

theorem uniformCauchy_of_time_holder
    (f : ℝ → A → F) (S : Set A) (I : Set ℝ)
    {C γ : ℝ} (hγ : 0 < γ)
    (hHolder : ∀ s ∈ I, ∀ t ∈ I, ∀ x ∈ S,
      ‖f s x - f t x‖ ≤ C * |s - t| ^ γ)
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ I) (hCauchy : CauchySeq τ) :
    UniformCauchySeqOn (fun m x => f (τ m) x) atTop S := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hCont : ContinuousAt (fun d : ℝ => C * |d| ^ γ) 0 :=
    continuousAt_const.mul (continuous_abs.continuousAt.rpow_const (Or.inr hγ.le))
  have hSmall : ∀ᶠ d : ℝ in 𝓝 0, C * |d| ^ γ < ε := by
    have hT : Tendsto (fun d : ℝ => C * |d| ^ γ) (𝓝 0) (𝓝 0) := by
      change Tendsto (fun d : ℝ => C * |d| ^ γ) (𝓝 0) (𝓝 (C * |(0 : ℝ)| ^ γ)) at hCont
      simpa only [abs_zero, Real.zero_rpow hγ.ne', mul_zero] using hCont
    exact hT.eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp hSmall
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hCauchy δ hδ
  refine ⟨N, ?_⟩
  intro m hm n hn x hx
  have hd : τ m - τ n ∈ ball (0 : ℝ) δ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, Real.dist_eq] using hN m hm n hn
  exact (show dist (f (τ m) x) (f (τ n) x) ≤ C * |τ m - τ n| ^ γ by
    simpa only [dist_eq_norm] using hHolder (τ m) (hτ m) (τ n) (hτ n) x hx).trans_lt
      (hBall hd)

theorem uniform_limit_of_time_holder
    (f : ℝ → A → F) (S : Set A) (I : Set ℝ)
    {C γ : ℝ} (hγ : 0 < γ)
    (hHolder : ∀ s ∈ I, ∀ t ∈ I, ∀ x ∈ S,
      ‖f s x - f t x‖ ≤ C * |s - t| ^ γ)
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ I) (hCauchy : CauchySeq τ) :
    ∃ g : A → F, TendstoUniformlyOn (fun m x => f (τ m) x) g atTop S := by
  classical
  have hUC := uniformCauchy_of_time_holder f S I hγ hHolder τ hτ hCauchy
  have hExists (x : A) (hx : x ∈ S) :
      ∃ y : F, Tendsto (fun m => f (τ m) x) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (hUC.cauchySeq hx)
  let g : A → F := fun x => if hx : x ∈ S then Classical.choose (hExists x hx) else 0
  refine ⟨g, hUC.tendstoUniformlyOn_of_tendsto ?_⟩
  intro x hx
  simpa only [g, dif_pos hx] using Classical.choose_spec (hExists x hx)

end Yau.NodeProofs.F01Aux
