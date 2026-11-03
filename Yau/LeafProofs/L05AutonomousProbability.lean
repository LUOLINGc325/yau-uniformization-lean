import Yau.LeafProofs.L05AutonomousAverageStability
import Mathlib.Analysis.Convex.Integral
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- These are actual measurable finite partitions: each cell is a fiber of the
simple function, and every sampled value is a value of the original function. -/
theorem auto_probability_partition_approx {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → E)
    (hg : StronglyMeasurable g) (hgi : Integrable g μ) :
    ∃ G : ℕ → SimpleFunc α E,
      (∀ j x, G j x∈range g) ∧
      (∀ j, Integrable (G j) μ) ∧
      (∀ j v, MeasurableSet ((G j) ⁻¹' {v})) ∧
      (∀ j, ∑ v∈(G j).range, μ.real ((G j) ⁻¹' {v})=1) ∧
      Tendsto (fun j => (G j).integral μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  classical
  borelize E
  letI : TopologicalSpace.SeparableSpace (range g) := hg.isSeparable_range.separableSpace
  obtain ⟨x0,_⟩ := (ae_of_all μ fun _ : α => True.intro).exists
  let G : ℕ → SimpleFunc α E := SimpleFunc.approxOn g hg.measurable (range g) (g x0) (mem_range_self x0)
  refine ⟨G,?_,?_,?_,?_,?_⟩
  · exact fun j x => SimpleFunc.approxOn_mem hg.measurable (mem_range_self x0) j x
  · exact SimpleFunc.integrable_approxOn hg.measurable hgi (mem_range_self x0) (integrable_const _)
  · exact fun j v => (G j).measurableSet_fiber v
  · intro j
    simp_rw [measureReal_def]
    rw [← ENNReal.toReal_sum,(G j).sum_range_measure_preimage_singleton,measure_univ,ENNReal.toReal_one]
    finiteness
  exact tendsto_integral_approxOn_of_measurable hgi hg.measurable
    (ae_of_all μ fun x => subset_closure (mem_range_self x)) (mem_range_self x0) (integrable_const _)

/-- Norm convergence of actual bounded continuous functions is uniform on all points. -/
theorem auto_bcf_tendsto_uniform {n : ℕ} {v : ℕ → (Point n →ᵇ ℝ)} {u : Point n →ᵇ ℝ}
    (hlim : Tendsto v atTop (𝓝 u)) :
    TendstoUniformlyOn (fun j p => v j p) (fun p => u p) atTop univ := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro eps heps
  filter_upwards [hlim (Metric.ball_mem_nhds u heps)] with j hj
  intro p _
  calc
    dist (u p) (v j p) ≤ dist u (v j) := BoundedContinuousFunction.dist_coe_le_dist p
    _ < eps := by
      change dist (v j) u<eps at hj
      simpa only [dist_comm] using hj

/-- The pointwise integral is the evaluation of a genuine Bochner integral in the Banach space. -/
theorem auto_bcf_integral_apply {n : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → (Point n →ᵇ ℝ)} (hgi : Integrable g μ) (p : Point n) :
    (∫ x, g x ∂μ) p=∫ x, g x p ∂μ := by
  exact ((BoundedContinuousFunction.evalCLM ℝ p).integral_comp_comm hgi).symm

/-- Probability averaging is proved using its finite measurable partition sums,
followed by the actual locally uniform viscosity stability theorem. -/
theorem auto_bcf_probability_sub {n : ℕ} {α : Type*} [MeasurableSpace α]
    {Q : Set (Point n)} {ell L : ℝ} {F : Sym n → ℝ}
    (hQ : IsOpen Q) (hell : 0≤ell) (hL : ell≤L) (hF : Continuous F)
    (hE : globalElliptic F ell L) (hC : ConcaveOn ℝ univ F)
    (μ : Measure α) [IsProbabilityMeasure μ] (g : α → (Point n →ᵇ ℝ))
    (hg : StronglyMeasurable g) (hgi : Integrable g μ)
    (hsub : ∀ x, viscositySub Q (fun H _ => F H) (fun _ => 0) (fun p => g x p)) :
    viscositySub Q (fun H _ => F H) (fun _ => 0) (fun p => ∫ x, g x p ∂μ) := by
  classical
  obtain ⟨G,hGrange,hGint,hGmeas,hGsum,hGlim⟩ := auto_probability_partition_approx μ g hg hgi
  have hfinite (j : ℕ) : viscositySub Q (fun H _ => F H) (fun _ => 0)
      (fun p => ((G j).integral μ) p) := by
    have hsample (v : Point n →ᵇ ℝ) (hv : v∈(G j).range) :
        viscositySub Q (fun H _ => F H) (fun _ => 0) (fun p => v p) := by
      obtain ⟨x,rfl⟩ := SimpleFunc.mem_range.mp hv
      obtain ⟨y,hy⟩ := hGrange j x
      rw [← hy]
      exact hsub y
    have hh := auto_finite_probability_sub (G j).range hQ hell hL hE hC
      (fun v => μ.real ((G j) ⁻¹' {v})) (fun _ _ => ENNReal.toReal_nonneg) (hGsum j)
      (fun v : Point n →ᵇ ℝ => fun p => v p)
      (fun v _ => v.continuous.continuousOn) hsample
    have heq : (fun p => ((G j).integral μ) p)=
        (fun p => ∑ v∈(G j).range, μ.real ((G j) ⁻¹' {v})*v p) := by
      funext p
      rw [SimpleFunc.integral_eq]
      simp only [BoundedContinuousFunction.sum_apply,BoundedContinuousFunction.smul_apply,smul_eq_mul]
    rw [heq]
    exact hh.2
  have hlim := (auto_bcf_tendsto_uniform hGlim).mono (subset_univ Q)
  have hres := auto_locally_uniform_sub hQ hF
    (fun j => ((G j).integral μ).continuous.continuousOn) hfinite hlim.tendstoLocallyUniformlyOn
  simpa only [auto_bcf_integral_apply hgi] using hres

end Yau.LeafProofs.L05AutonomousAux
