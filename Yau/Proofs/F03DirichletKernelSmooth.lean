import Yau.Proofs.F03DirichletRieszSmooth
import Yau.Proofs.F03DirichletRieszKernel

/-! The actual single kernel is jointly C-infinity in both points and time. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletKernelCandidate_smooth (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) :
    KernelSmoothOn Ω (dirichletKernelCandidate g hK μ hμ Ω hΩ) := by
  intro a b
  let Q := ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ
    {z | z ∈ chartTarget b ∧ chartInv b z ∈ Ω}) ×ˢ Set.Ioi (0 : ℝ)
  have hL : ContDiff ℝ ∞
      (fun p : (ComplexVector n × ComplexVector n) × ℝ => (p.1.1,p.2/2)) := by
    fun_prop
  have hR : ContDiff ℝ ∞
      (fun p : (ComplexVector n × ComplexVector n) × ℝ => (p.1.2,p.2/2)) := by
    fun_prop
  have hLa := (dirichletChartRieszVector_smooth g hK μ hμ Ω hΩ a).comp
    hL.contDiffOn (show MapsTo (fun p : (ComplexVector n × ComplexVector n) × ℝ => (p.1.1,p.2/2))
      Q ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) from
      fun p hp => ⟨hp.1.1,(half_pos (show 0 < p.2 from hp.2) : 0 < p.2/2)⟩)
  have hRb := (dirichletChartRieszVector_smooth g hK μ hμ Ω hΩ b).comp
    hR.contDiffOn (show MapsTo (fun p : (ComplexVector n × ComplexVector n) × ℝ => (p.1.2,p.2/2))
      Q ({z | z ∈ chartTarget b ∧ chartInv b z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)) from
      fun p hp => ⟨hp.1.2,(half_pos (show 0 < p.2 from hp.2) : 0 < p.2/2)⟩)
  apply (hLa.inner ℝ hRb).congr
  intro p hp
  have ht : 0 < p.2 := hp.2
  have hh : 0 < p.2/2 := half_pos ht
  simp only [Function.comp_def]
  rw [dirichletChartRieszVector_eq g hK μ hμ Ω hΩ a (p.1.1,p.2/2)
    ⟨hp.1.1,hh⟩,
    dirichletChartRieszVector_eq g hK μ hμ Ω hΩ b (p.1.2,p.2/2)
    ⟨hp.1.2,hh⟩,
    dirichletKernelCandidate_of_members g hK μ hμ Ω hΩ ht
      (chartInv a p.1.1) (chartInv b p.1.2) hp.1.1.2 hp.1.2.2]

end Yau.Proofs.F03Aux
