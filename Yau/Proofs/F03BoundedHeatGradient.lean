import Yau.Proofs.F03BoundedHeatOrder
import Yau.Proofs.F03BoundedHeatEquation
import Yau.Proofs.F03NonnegativeHeatGradient

/-! The first gradient majorant is proved for the actual same-kernel bounded nonnegative evolution. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalBoundedHeat_gradient_bound
    (g : SmoothMetric M) (hK : IsKahler g) (hRic : ∀ z,(ricci g.form z).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ y,|f y| ≤ B) (hNonnegative : ∀ y,0 ≤ f y)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (gradNormSq g.form (fun z => boundedKernelEvolution μ
      (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t z) x) ≤
      LeafProofs.L24Aux.localGradientConstant n*B/Real.sqrt t := by
  apply nonnegative_heat_gradient_at_sqrt_scale g hK hRic
    (fun z b => boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO) f b z)
    (dirichletMinimalBoundedHeat_smooth g hK μ hμ O hO f hf B hB hBound)
    (fun z b hb => dirichletMinimalBoundedHeat_hasDerivAt g hK μ hμ O hO f hf B hB hBound z hb)
    (fun z b hb => dirichletMinimalBoundedHeat_nonnegative g hK μ hμ O hO f hNonnegative hb.le z)
    x ht hB.le
  intro z s _hz hs
  have hs0 : 0 < s := lt_of_lt_of_le (half_pos ht) hs.1
  exact (le_abs_self _).trans
    (dirichletMinimalKernelCandidate_bounded_evolution_le g hK μ hμ O hO f hf B hB.le hBound hs0 z).2

end Yau.Proofs.F03Aux
