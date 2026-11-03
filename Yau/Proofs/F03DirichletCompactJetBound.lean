import Yau.Proofs.F03DirichletCompactJetTesting
import Yau.Proofs.F03CompactTestSeparation
import Yau.Proofs.F03ClosedGraphTests

/-! Actual compact-cylinder finite-jet bounds chosen before every source. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Genuine compact tests give the closed graph and hence actual
continuity of the full source-to-continuous-value map. -/
theorem dirichletCompactHeatJet_continuous (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget a) (hOΩ : chartInv a '' O ⊆ Ω)
    {l r : ℝ} (hl : 0 < l)
    (K : Set (Parabolic.Point n)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Parabolic.Point n))]
    (hKc : IsCompact K) (hreg : K = closure (interior K))
    (hbuffer : K ⊆ O ×ˢ Set.Ioo l r)
    (hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
    (w : List (Parabolic.Point n)) :
    Continuous (dirichletCompactHeatJet g hK μ hμ Ω hΩ a K hKQ w) := by
  let ι := {φ : Parabolic.Point n → ℝ // Parabolic.Test (interior K) φ}
  let hTest : ∀ φ : ι, Parabolic.Test (O ×ˢ Set.Ioo l r) φ.val := fun φ =>
    ⟨φ.property.1,φ.property.2.1,φ.property.2.2.trans (interior_subset.trans hbuffer)⟩
  let A : ι → C(K,ℝ) →L[ℝ] ℝ := fun φ => compactTestFunctional K
    (volume.comap ((↑) : K → Parabolic.Point n))
    (compactContinuousRestriction K φ.val φ.property.1.continuous.continuousOn)
  let B : ι → Lp ℝ 2 (μ.restrict Ω) →L[ℝ] ℝ := fun φ =>
    (-1 : ℝ)^w.length • dirichletChartTestOperator g μ hμ Ω hΩ.measurableSet a (subset_closure.trans hOt)
      (scalarChart_densityInverseTest g a (subset_closure.trans hOt)
        (test_directionalWordDerivative (hTest φ) w.reverse))
  apply linearMap_continuous_of_tests (dirichletCompactHeatJet g hK μ hμ Ω hΩ a K hKQ w) A B
  · intro q hq
    apply compactTestFunctional_separates K hKc hreg q
    intro φ hφ
    exact hq ⟨φ,hφ⟩
  · intro φ f
    exact dirichletCompactHeatJet_test g hK μ hμ Ω hΩ a hO hOc hOt hOΩ hl K
      hKc.measurableSet hKQ w (hTest φ) (φ.property.2.2.trans interior_subset) f

/-- One finite constant is chosen from the proved bounded operator BEFORE
all input sources and all points of the actual compact cylinder. -/
theorem dirichletClassicalHeat_compact_jet_bound (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a : M.Carrier)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget a) (hOΩ : chartInv a '' O ⊆ Ω)
    {l r : ℝ} (hl : 0 < l)
    (K : Set (Parabolic.Point n)) [CompactSpace K]
    [IsFiniteMeasure (volume.comap ((↑) : K → Parabolic.Point n))]
    (hKc : IsCompact K) (hreg : K = closure (interior K))
    (hbuffer : K ⊆ O ×ˢ Set.Ioo l r)
    (hKQ : K ⊆ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ))
    (w : List (Parabolic.Point n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (μ.restrict Ω), ∀ p ∈ K,
      |directionalWordDerivative (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f) w p| ≤ C * ‖f‖ := by
  let L : Lp ℝ 2 (μ.restrict Ω) →L[ℝ] C(K,ℝ) :=
    ⟨dirichletCompactHeatJet g hK μ hμ Ω hΩ a K hKQ w,
      dirichletCompactHeatJet_continuous g hK μ hμ Ω hΩ a hO hOc hOt hOΩ hl K hKc hreg hbuffer hKQ w⟩
  refine ⟨max 1 ‖L‖,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro f p hp
  have hv := (L f).norm_coe_le_norm (⟨p,hp⟩ : K)
  change |directionalWordDerivative (dirichletClassicalChartHeat g hK μ hμ Ω hΩ a f) w p| ≤ ‖L f‖ at hv
  exact hv.trans ((L.le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 ‖L‖) (norm_nonneg f)))

end Yau.Proofs.F03Aux
