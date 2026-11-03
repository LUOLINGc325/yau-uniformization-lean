import Yau.Proofs.F03MinimalBoundedEvolution
import Yau.Proofs.F03MinimalKernelL2Action

/-! Actual restricted-L² data and dominated integral convergence for arbitrary bounded measurable sources. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem bounded_source_precompact_scalarL2
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ y,|f y| ≤ B) :
    ScalarL2 (μ.restrict Ω) f := by
  letI : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.mpr
    (smoothPrecompactDomain_volume_lt_top g μ hμ Ω hΩ).ne
  apply (scalarL2_iff_memLp _ _).mpr
  exact (memLp_const B).mono' hf.restrict
    (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs,abs_of_nonneg hB] using hBound y))

theorem dirichletExhaustionKernels_bounded_integral_tendsto
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 ≤ B) (hBound : ∀ y,|f y| ≤ B)
    {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    Tendsto (fun j => ∫ y,dirichletExhaustionKernels g hK μ hμ O hO j t x y*f y ∂μ) atTop
      (𝓝 (∫ y,dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun y => dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*B)
  · intro j
    exact (dirichletKernelCandidate_mass g hK μ hμ (O j) (hO.1 j) ht x).1.aestronglyMeasurable.mul hf
  · exact (dirichletMinimalKernelCandidate_mass g hK μ hμ O hO ht x).1.mul_const B
  · intro j
    filter_upwards [] with y
    change |dirichletExhaustionKernels g hK μ hμ O hO j t x y*f y| ≤ _
    have hn : 0 ≤ dirichletExhaustionKernels g hK μ hμ O hO j t x y :=
      dirichletKernelCandidate_nonneg g hK μ hμ (O j) (hO.1 j).1 ht x y
    rw [abs_mul,abs_of_nonneg hn]
    exact (mul_le_mul_of_nonneg_left (hBound y) hn).trans
      (mul_le_mul_of_nonneg_right (dirichletExhaustionKernels_le_limit g hK μ hμ O hO ht x y j) hB)
  · exact ae_of_all μ (fun y =>
      (dirichletExhaustionKernels_tendsto g hK μ hμ O hO ht x y).mul_const (f y))

end Yau.Proofs.F03Aux
