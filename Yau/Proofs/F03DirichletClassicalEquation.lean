import Yau.Proofs.F03DirichletClassicalHeat
import Yau.Proofs.F03C2Laplacian

/-! The original total Laplacian equation for the actual interior representative. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
open LeafProofs
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletHeat_chart_linearOp_residual (g : SmoothMetric M)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {u : M.Carrier → ℝ → ℝ}
    (hu : ∀ a : M.Carrier, ContDiffOn ℝ ∞
      (fun p : Parabolic.Point n => u (chartInv a p.1) p.2)
      ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi 0))
    (y : M.Carrier) (hy : y ∈ Ω) {t : ℝ} (ht : 0 < t) :
    Parabolic.linearOp ({z | z ∈ chartTarget y ∧ chartInv y z ∈ Ω} ×ˢ Set.Ioi 0)
      (scalarHeatChartCoeff g y) (fun _ _ => 0)
      (fun p : Parabolic.Point n => u (chartInv y p.1) p.2) (chartPt y y,t) =
        deriv (u y) t - laplacian g.form (fun z => u z t) y := by
  let F : Parabolic.Point n → ℝ := fun p => u (chartInv y p.1) p.2
  let Q := {z | z ∈ chartTarget y ∧ chartInv y z ∈ Ω} ×ˢ Set.Ioi (0 : ℝ)
  have hQ : IsOpen Q := (dirichletChartInterior_open Ω hΩ y).prod isOpen_Ioi
  have hinv : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hp : (chartPt y y,t) ∈ Q := ⟨⟨mem_extChartAt_target y,by rwa [hinv]⟩,ht⟩
  have htwo : ContDiffAt ℝ 2 (inChart y (fun z => u z t)) (chartPt y y) :=
    (((hu y).contDiffAt (hQ.mem_nhds hp)).comp (chartPt y y)
      (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  have hL : laplacian g.form (fun z => u z t) y =
      ∑ i, ∑ j, scalarHeatChartCoeff g y (chartPt y y,t) i j *
        Parabolic.spatialDD F (chartPt y y,t) (realVec i) (realVec j) := by
    have hh := laplacian_c2_principal g.form (fun z => u z t) y htwo
    have hChart : inChart y (fun z => u z t) = (fun z => u (chartInv y z) t) := rfl
    rw [hChart] at hh
    symm
    calc
      _ = (1/2 : ℝ) * (∑ i, ∑ j, (realMetricFn g.form y (chartPt y y))⁻¹ i j *
          fderiv ℝ (fderiv ℝ (fun z => u (chartInv y z) t)) (chartPt y y) (realVec i) (realVec j)) := by
        simp only [scalarHeatChartCoeff,Parabolic.spatialDD,F,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = laplacian g.form (fun z => u z t) y := by rw [hh]; ring
  change Parabolic.linearOp Q (scalarHeatChartCoeff g y) (fun _ _ => 0) F (chartPt y y,t) = _
  unfold Parabolic.linearOp
  rw [L16Aux.timeD_eq_deriv_of_isOpen hQ hp]
  simp only [zero_mul,Finset.sum_const_zero,sub_zero]
  rw [← hL]
  simp only [F,hinv]

/-- The locally smooth actual representative solves the original scalar
heat equation, including the total calculator Laplacian of its zero extension. -/
theorem dirichletClassicalHeat_equation (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (y : M.Carrier) (hy : y ∈ Ω) {t : ℝ} (ht : 0 < t) :
    deriv (dirichletClassicalHeat g hK μ hμ Ω hΩ f y) t =
      laplacian g.form (fun z => dirichletClassicalHeat g hK μ hμ Ω hΩ f z t) y := by
  let u := dirichletClassicalHeat g hK μ hμ Ω hΩ f
  have hGerm := (dirichletHeat_exists_globalRepresentative (complexManifold_dimension_pos M)
    g hK μ hμ Ω hΩ f).choose_spec.2.2.2
  obtain ⟨Q,v,hQ,hpQ,_hv,hEq,hClass⟩ := hGerm y hy t ht
  have hinv : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hp : (chartPt y y,t) ∈ {z | z ∈ chartTarget y ∧ chartInv y z ∈ Ω} ×ˢ Set.Ioi 0 :=
    ⟨⟨mem_extChartAt_target y,by rwa [hinv]⟩,ht⟩
  have hOp := L16Aux.linearOp_congr_open_sets
    ((dirichletChartInterior_open Ω hΩ y).prod isOpen_Ioi) hQ
    (scalarHeatChartCoeff g y) (fun _ _ => 0) hp hpQ hEq
  have hzero := hOp.trans hClass
  change Parabolic.linearOp ({z | z ∈ chartTarget y ∧ chartInv y z ∈ Ω} ×ˢ Set.Ioi 0)
    (scalarHeatChartCoeff g y) (fun _ _ => 0)
    (fun p : Parabolic.Point n => dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv y p.1) p.2)
    (chartPt y y,t) = 0 at hzero
  rw [dirichletHeat_chart_linearOp_residual g Ω hΩ
    (dirichletClassicalHeat_smooth g hK μ hμ Ω hΩ f) y hy ht] at hzero
  exact sub_eq_zero.mp hzero

/-- Actual classical time differentiability is proved on the interior;
the value of its derivative is the original project Laplacian. -/
theorem dirichletClassicalHeat_hasDerivAt (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (y : M.Carrier) (hy : y ∈ Ω) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (dirichletClassicalHeat g hK μ hμ Ω hΩ f y)
      (laplacian g.form (fun z => dirichletClassicalHeat g hK μ hμ Ω hΩ f z t) y) t := by
  have hinv : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have hp : (chartPt y y,t) ∈ {z | z ∈ chartTarget y ∧ chartInv y z ∈ Ω} ×ˢ Set.Ioi 0 :=
    ⟨⟨mem_extChartAt_target y,by rwa [hinv]⟩,ht⟩
  have hc := ((dirichletClassicalHeat_smooth g hK μ hμ Ω hΩ f y).contDiffAt
    (((dirichletChartInterior_open Ω hΩ y).prod isOpen_Ioi).mem_nhds hp)).comp t
      (contDiffAt_const.prodMk contDiffAt_id)
  have hd : DifferentiableAt ℝ (dirichletClassicalHeat g hK μ hμ Ω hΩ f y) t := by
    simpa only [Function.comp_def,hinv] using hc.differentiableAt (by simp)
  rw [← dirichletClassicalHeat_equation g hK μ hμ Ω hΩ f y hy ht]
  exact hd.hasDerivAt

end Yau.Proofs.F03Aux
