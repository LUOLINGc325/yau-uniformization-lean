import Yau.Proofs.F03MinimalKernelMass

/-! The same exhaustion limit acts integrably on every actual ambient L² source. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem dirichletMinimalKernelCandidate_l2_source_integrable
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : ScalarL2 μ f) {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    Integrable (fun y => dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y) μ := by
  have hfa : ScalarL2 (μ.restrict univ) (fun y => |f y|) :=
    (scalarL2_iff_memLp _ _).mpr (((scalarL2_iff_memLp _ _).mp hf).abs.restrict univ)
  have hmajor := dirichletKernelCandidate_source_integrable g hK μ hμ univ isOpen_univ ht
    x (mem_univ x) (fun y => |f y|) hfa
  apply hmajor.mono'
    ((dirichletMinimalKernelCandidate_mass g hK μ hμ O hO ht x).1.aestronglyMeasurable.mul hf.1)
  filter_upwards [] with y
  change |dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y| ≤ _
  rw [abs_mul,abs_of_nonneg (dirichletMinimalKernelCandidate_nonneg g hK μ hμ O hO ht x y)]
  exact mul_le_mul_of_nonneg_right
    (dirichletMinimalKernelCandidate_le_univ g hK μ hμ O hO ht x y) (abs_nonneg _)

theorem dirichletExhaustionKernels_l2_integral_tendsto
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : ScalarL2 μ f) {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    Tendsto (fun j => ∫ y, dirichletExhaustionKernels g hK μ hμ O hO j t x y*f y ∂μ) atTop
      (𝓝 (∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y ∂μ)) := by
  have hfa : ScalarL2 (μ.restrict univ) (fun y => |f y|) :=
    (scalarL2_iff_memLp _ _).mpr (((scalarL2_iff_memLp _ _).mp hf).abs.restrict univ)
  apply tendsto_integral_of_dominated_convergence
    (fun y => dirichletKernelCandidate g hK μ hμ univ isOpen_univ t x y*|f y|)
  · intro j
    exact (dirichletKernelCandidate_mass g hK μ hμ (O j) (hO.1 j) ht x).1.aestronglyMeasurable.mul hf.1
  · exact dirichletKernelCandidate_source_integrable g hK μ hμ univ isOpen_univ ht
      x (mem_univ x) (fun y => |f y|) hfa
  · intro j
    filter_upwards [] with y
    change |dirichletExhaustionKernels g hK μ hμ O hO j t x y*f y| ≤ _
    have hn : 0 ≤ dirichletExhaustionKernels g hK μ hμ O hO j t x y :=
      dirichletKernelCandidate_nonneg g hK μ hμ (O j) (hO.1 j).1 ht x y
    rw [abs_mul,abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_right
      (dirichletExhaustionKernels_le_univ g hK μ hμ O hO ht x y j) (abs_nonneg _)
  · exact ae_of_all μ (fun y =>
      (dirichletExhaustionKernels_tendsto g hK μ hμ O hO ht x y).mul_const (f y))

end Yau.Proofs.F03Aux
