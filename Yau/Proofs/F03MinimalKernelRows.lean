import Yau.Proofs.F03MinimalNativeHeatAction

/-! Actual L² rows and the exact L² class of the minimal-kernel integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletMinimalKernelCandidate_row_scalarL2
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) : ScalarL2 μ (dirichletMinimalKernelCandidate g hK μ hμ O hO t x) := by
  have hu : MemLp (dirichletKernelCandidate g hK μ hμ univ isOpen_univ t x) 2 μ := by
    simpa only [Measure.restrict_univ] using (scalarL2_iff_memLp _ _).mp
      (dirichletKernelCandidate_row_scalarL2 g hK μ hμ univ isOpen_univ ht x (mem_univ x))
  apply (scalarL2_iff_memLp _ _).mpr
  apply hu.mono' (dirichletMinimalKernelCandidate_mass g hK μ hμ O hO ht x).1.aestronglyMeasurable
  filter_upwards [] with y
  change |dirichletMinimalKernelCandidate g hK μ hμ O hO t x y| ≤ _
  rw [abs_of_nonneg (dirichletMinimalKernelCandidate_nonneg g hK μ hμ O hO ht x y)]
  exact dirichletMinimalKernelCandidate_le_univ g hK μ hμ O hO ht x y

theorem dirichletMinimalKernelCandidate_action_scalarL2
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) (f : Lp ℝ 2 μ)
    {t : ℝ} (ht : 0 < t) : ScalarL2 μ
      (fun x => ∫ y, dirichletMinimalKernelCandidate g hK μ hμ O hO t x y*f y ∂μ) := by
  apply (scalarL2_iff_memLp _ _).mpr
  exact MemLp.ae_eq (dirichletMinimalKernelCandidate_native_heat_ae g hK μ hμ O hO f ht).symm (Lp.memLp _)

theorem dirichletMinimalKernelCandidate_action_toLp
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) (f : Lp ℝ 2 μ)
    {t : ℝ} (ht : 0 < t) :
    scalarToLp (dirichletMinimalKernelCandidate_action_scalarL2 g hK μ hμ O hO f ht)=
      scalarHeatFamily g μ hμ t f := by
  apply Lp.ext
  exact (scalarToLp_coe _).trans (dirichletMinimalKernelCandidate_native_heat_ae g hK μ hμ O hO f ht)

end Yau.Proofs.F03Aux
