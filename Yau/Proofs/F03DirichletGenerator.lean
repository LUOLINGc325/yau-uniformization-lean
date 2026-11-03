import Yau.Proofs.F03DirichletComplexGenerator
import Yau.Proofs.F03DirichletFriedrichs
import Yau.Proofs.F03DirichletHeat

/-! Both-direction real generator identification with the literal supported Friedrichs graph. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {M : ComplexManifold n}

theorem dirichlet_generator_iff (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier) (hO : IsOpen O)
    (f w : Lp ℝ 2 (μ.restrict O)) :
    f = dirichletResolvent g μ hμ O (f + w) ↔
      Tendsto (fun t : ℝ => t⁻¹ • (dirichletHeat g μ hμ O t f - f) + w)
        (𝓝[>] 0) (𝓝 0) := by
  let ν := μ.restrict O
  let I := heatLpOfReal ν
  have hI : Function.Injective I := Function.LeftInverse.injective (heatLpRe_ofReal ν)
  have hgraph : f = dirichletResolvent g μ hμ O (f + w) ↔
      I f = dirichletComplexResolvent g μ hμ O (I f + I w) := by
    rw [← map_add I f w, dirichletComplexResolvent_ofReal]
    exact hI.eq_iff.symm
  rw [hgraph, dirichletComplex_generator_iff g μ hμ O hO (I f) (I w)]
  constructor
  · intro h
    have hr := (heatLpRe ν).continuous.tendsto 0 |>.comp h
    simpa only [Function.comp_def, map_zero, map_add, map_smul, map_sub,
      I, ν, heatLpRe_ofReal, ← dirichletHeat_apply] using hr
  · intro h
    have hc := I.continuous.tendsto 0 |>.comp h
    simpa only [Function.comp_def, map_zero, map_add, map_smul, map_sub,
      I, ν, dirichletHeat_ofReal] using hc

/-- This is the exact actual prequotient graph, with no generator-domain
inlet and with both initial-limit directions proved. Kernel representation
will identify this same family with the single constructed kernel. -/
theorem scalarFriedrichsPair_iff_heat_generator (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (hO : IsOpen O) (f w : M.Carrier → ℝ)
    (hf : ScalarL2 (μ.restrict O) f) (hw : ScalarL2 (μ.restrict O) w) :
    ScalarFriedrichsPair g.form μ O f w ↔
      Tendsto (fun t : ℝ => t⁻¹ •
        (dirichletHeat g μ hμ O t (scalarToLp hf) - scalarToLp hf) + scalarToLp hw)
          (𝓝[>] 0) (𝓝 0) :=
  (scalarFriedrichsPair_iff_resolvent g μ hμ O f w hf hw).trans
    (dirichlet_generator_iff g μ hμ O hO (scalarToLp hf) (scalarToLp hw))

end Yau.Proofs.F03Aux
