import Yau.Proofs.F03DirichletChartEquation
import Yau.Proofs.F03DirichletKernelProducer

/-! The true kernel satisfies the same computed PDE at every chart point. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic LeafProofs.L16Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

theorem subTimeShift_linearOp {O : Set (Space n)} (hO : IsOpen O)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioi (0 : ℝ)))
    (a : Point n → Mat n) (σ : ℝ) (p : Point n) (hp : p ∈ O ×ˢ Ioi σ) :
    linearOp (O ×ˢ Ioi σ) (fun q => a (q.1,q.2-σ)) (fun _ _ => 0)
      (fun q => u (q.1,q.2-σ)) p =
      linearOp (O ×ˢ Ioi (0 : ℝ)) a (fun _ _ => 0) u (p.1,p.2-σ) := by
  have hpσ : σ < p.2 := hp.2
  have ht : 0 < p.2-σ := sub_pos.mpr hpσ
  have hq : (p.1,p.2-σ) ∈ O ×ˢ Ioi (0 : ℝ) := ⟨hp.1,ht⟩
  have hd : DifferentiableAt ℝ (fun s => u (p.1,s)) (p.2-σ) :=
    ((hu.contDiffAt ((hO.prod isOpen_Ioi).mem_nhds hq)).comp (p.2-σ)
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hdt : deriv (fun s => u (p.1,s-σ)) p.2=deriv (fun s => u (p.1,s)) (p.2-σ) := by
    have h := hd.hasDerivAt.comp p.2 ((hasDerivAt_id p.2).sub_const σ)
    simpa only [Function.comp_def,id_eq,mul_one] using h.deriv
  unfold linearOp
  rw [timeD_eq_deriv_of_isOpen (hO.prod isOpen_Ioi) hp,
    timeD_eq_deriv_of_isOpen (hO.prod isOpen_Ioi) hq,hdt]
  simp only [zero_mul,Finset.sum_const_zero,sub_zero]
  rfl

theorem dirichletKernelCandidate_chart_equation
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (a y : M.Carrier) (hy : y ∈ Ω)
    (p : Point n) (hp : p ∈ {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Ioi (0 : ℝ)) :
    linearOp ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Ioi (0 : ℝ))
      (scalarHeatChartCoeff g a) (fun _ _ => 0)
      (fun q : Point n => dirichletKernelCandidate g hK μ hμ Ω hΩ q.2 (chartInv a q.1) y) p=0 := by
  let D := {z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω}
  have hD : IsOpen D := dirichletChartInterior_open Ω hΩ a
  let σ := p.2/2
  have hσ : 0 < σ := half_pos hp.2
  have hσp : σ < p.2 := half_lt_self hp.2
  let v := dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy σ hσ
  let F : Point n → ℝ := fun q => dirichletKernelCandidate g hK μ hμ Ω hΩ q.2 (chartInv a q.1) y
  let V := dirichletClassicalChartHeat g hK μ hμ Ω hΩ a v
  have hEq : F =ᶠ[𝓝 p] (fun q : Point n => V (q.1,q.2-σ)) := by
    filter_upwards [(hD.prod isOpen_Ioi).mem_nhds (show p ∈ D ×ˢ Ioi σ from ⟨hp.1,hσp⟩)] with q hq
    exact congrFun (dirichletKernelCandidate_split_heat g hK μ hμ Ω hΩ hσ hq.2 y hy) (chartInv a q.1)
  have hOp := linearOp_congr_open_sets (hD.prod isOpen_Ioi) (hD.prod isOpen_Ioi)
    (scalarHeatChartCoeff g a) (fun _ _ => 0) hp
    (show p ∈ D ×ˢ Ioi σ from ⟨hp.1,hσp⟩) hEq
  have hShift := subTimeShift_linearOp hD (dirichletClassicalChartHeat_smooth g hK μ hμ Ω hΩ a v)
    (scalarHeatChartCoeff g a) σ p ⟨hp.1,hσp⟩
  have hClass := dirichletClassicalChartHeat_equation g hK μ hμ Ω hΩ a v (p.1,p.2-σ)
    ⟨hp.1,sub_pos.mpr hσp⟩
  exact hOp.trans (hShift.trans hClass)

end Yau.Proofs.F03Aux
