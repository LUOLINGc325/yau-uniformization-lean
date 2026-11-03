import Yau.Proofs.F04DirichletCore
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology InnerProductSpace ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux

/-- An injective Hilbert inclusion into a separable pivot already forces
the original energy Hilbert space to be separable, by its dense adjoint range. -/
theorem hilbert_separable_of_injective_pivot
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
    (j : V →L[ℝ] H) (hj : Function.Injective j) : SeparableSpace V := by
  have hker : j.ker = ⊥ := LinearMap.ker_eq_bot.mpr hj
  have hcl : j.adjoint.range.topologicalClosure = ⊤ := by
    rw [← j.orthogonal_ker, hker, Submodule.bot_orthogonal_eq_top]
  have hd : DenseRange j.adjoint := by
    apply dense_iff_closure_eq.mpr
    change closure (j.adjoint.range : Set V) = univ
    rw [← Submodule.topologicalClosure_coe, hcl]
    rfl
  exact hd.separableSpace j.adjoint.continuous

theorem dirichletEnergy_separable_on_finite_domain
    {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) (hO : MeasurableSet O) [IsFiniteMeasure (μ.restrict O)] :
    SeparableSpace (DirichletEnergy g μ hμ O) := by
  let := dirichletEnergy_completeSpace g μ hμ O
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℝ 2 (μ.restrict O)) := MeasureTheory.Lp.SecondCountableTopology
  exact hilbert_separable_of_injective_pivot (dirichletL2 g μ hμ O)
    (dirichletL2_injective g hK μ hμ O hO)

end Yau.F04Proof
