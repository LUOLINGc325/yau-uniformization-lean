import Yau.Proofs.F03MinimalKernelCandidate
import Yau.Proofs.F03MonotoneIntegral

/-! The original convolution identity passes to the actual increasing kernels. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

theorem dirichletMinimalKernelCandidate_semigroup (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x y : M.Carrier) :
    Integrable (fun z => dirichletMinimalKernelCandidate g hK μ hμ O hO a x z *
      dirichletMinimalKernelCandidate g hK μ hμ O hO b z y) μ ∧
      dirichletMinimalKernelCandidate g hK μ hμ O hO (a+b) x y =
        ∫ z, dirichletMinimalKernelCandidate g hK μ hμ O hO a x z *
          dirichletMinimalKernelCandidate g hK μ hμ O hO b z y ∂μ := by
  let f : ℕ → M.Carrier → ℝ := fun j z =>
    dirichletExhaustionKernels g hK μ hμ O hO j a x z *
      dirichletExhaustionKernels g hK μ hμ O hO j b z y
  let F : M.Carrier → ℝ := fun z => dirichletMinimalKernelCandidate g hK μ hμ O hO a x z *
    dirichletMinimalKernelCandidate g hK μ hμ O hO b z y
  have hi : ∀ j, Integrable (f j) μ := fun j =>
    dirichletKernelCandidate_convolution_integrable g hK μ hμ (O j) (hO.1 j).1 ha hb x y
  have hn : ∀ j z, 0 ≤ f j z := fun j z =>
    mul_nonneg (dirichletKernelCandidate_nonneg g hK μ hμ (O j) (hO.1 j).1 ha x z)
      (dirichletKernelCandidate_nonneg g hK μ hμ (O j) (hO.1 j).1 hb z y)
  have hmono : ∀ z, Monotone (fun j => f j z) := by
    intro z i j hij
    exact mul_le_mul
      (dirichletExhaustionKernels_monotone g hK μ hμ O hO ha x z hij)
      (dirichletExhaustionKernels_monotone g hK μ hμ O hO hb z y hij)
      (dirichletKernelCandidate_nonneg g hK μ hμ (O i) (hO.1 i).1 hb z y)
      (dirichletKernelCandidate_nonneg g hK μ hμ (O j) (hO.1 j).1 ha x z)
  have hlim : ∀ z, Tendsto (fun j => f j z) atTop (𝓝 (F z)) := fun z =>
    (dirichletExhaustionKernels_tendsto g hK μ hμ O hO ha x z).mul
      (dirichletExhaustionKernels_tendsto g hK μ hμ O hO hb z y)
  have hid : ∀ j, (∫ z, f j z ∂μ) =
      dirichletExhaustionKernels g hK μ hμ O hO j (a+b) x y := fun j =>
    (dirichletKernelCandidate_semigroup g hK μ hμ (O j) (hO.1 j).1 ha hb x y).symm
  have hbound : ∀ j, (∫ z, f j z ∂μ) ≤
      dirichletKernelCandidate g hK μ hμ Set.univ isOpen_univ (a+b) x y := by
    intro j
    rw [hid j]
    exact dirichletExhaustionKernels_le_univ g hK μ hμ O hO (add_pos ha hb) x y j
  have hF := (integrable_monotone_limit_of_integral_le μ f F _ hi hn hmono hlim hbound).1
  refine ⟨hF,?_⟩
  have hint := integral_tendsto_of_tendsto_of_monotone hi hF
    (ae_of_all μ hmono) (ae_of_all μ hlim)
  simp_rw [hid] at hint
  exact tendsto_nhds_unique (dirichletExhaustionKernels_tendsto g hK μ hμ O hO (add_pos ha hb) x y) hint

end Yau.Proofs.F03Aux
