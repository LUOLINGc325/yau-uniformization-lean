import Yau.LeafProofs.L19HeatRegularityGlobal

/-! A global classical representative of the actual scalar CFC heat,
with every positive-time actual L² slice and the original heat equation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The computed half-inverse-metric chart operator is exactly the
original heat residual in the actual centered chart. -/
theorem scalarHeat_chart_linearOp_residual (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (y : M.Carrier) {t : ℝ} (ht : 0 < t) :
    Parabolic.linearOp (chartTarget y ×ˢ Set.Ioi 0) (scalarHeatChartCoeff g y) (fun _ _ => 0)
      (fun p : Parabolic.Point n => u (chartInv y p.1) p.2) (chartPt y y,t) =
      deriv (u y) t - laplacian g.form (fun z => u z t) y := by
  let F : Parabolic.Point n → ℝ := fun p => u (chartInv y p.1) p.2
  have hslice := smoothSpaceTime_slice hu ht
  have htwo : ContDiffAt ℝ 2 (inChart y (fun z => u z t)) (chartPt y y) :=
    (contDiffAt_inChart hslice y (mem_extChartAt_target y)).of_le (by simp)
  have hL : laplacian g.form (fun z => u z t) y =
      ∑ i, ∑ j, scalarHeatChartCoeff g y (chartPt y y,t) i j *
        Parabolic.spatialDD F (chartPt y y,t) (realVec i) (realVec j) := by
    rw [laplacian_eq_half_principal g.form hslice]
    simp_rw [rDeriv_rDeriv_eq_hessian htwo]
    have hChart : inChart y (fun z => u z t) = (fun z => u (chartInv y z) t) := rfl
    rw [hChart]
    simp only [scalarHeatChartCoeff,Parabolic.spatialDD,F,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  change Parabolic.linearOp (chartTarget y ×ˢ Set.Ioi 0) (scalarHeatChartCoeff g y) (fun _ _ => 0)
    F (chartPt y y,t) = _
  unfold Parabolic.linearOp
  rw [L16Aux.timeD_eq_deriv_of_isOpen (Q := chartTarget y ×ˢ Set.Ioi 0) (u := F) (p := (chartPt y y,t))
    ((isOpen_extChartAt_target (I := ComplexModel n) y).prod isOpen_Ioi) ⟨mem_extChartAt_target y,ht⟩]
  simp only [zero_mul,Finset.sum_const_zero,sub_zero]
  rw [← hL]
  have hy : chartInv y (chartPt y y) = y := chartInv_chartPt_of_mem y y (mem_chart_source _ _)
  simp only [F,hy]

/-- The actual independently constructed scalar heat family has a global
smooth classical representative at all positive times. Every positive-time
slice represents the actual L² class, and its time derivative is the original
project Laplacian. No heat flow, smoothness, energy, mass or minimality datum
is supplied by the caller. -/
theorem scalarHeat_exists_classicalRepresentative (hn : 0 < n)
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : Lp ℝ 2 μ) :
    ∃ u : M.Carrier → ℝ → ℝ, SmoothSpaceTime u (Set.Ioi 0) ∧
      (∀ t > 0, (fun y => u y t) =ᵐ[μ] (scalarHeatFamily g μ hμ t f : M.Carrier → ℝ)) ∧
      ∀ (y : M.Carrier) (t : ℝ), 0 < t →
        deriv (u y) t = laplacian g.form (fun z => u z t) y := by
  obtain ⟨u,hu,hSlice,hGerm⟩ := scalarHeat_exists_globalRepresentative hn g hK μ hμ f
  refine ⟨u,hu,hSlice,?_⟩
  intro y t ht
  obtain ⟨Q,v,hQ,hpQ,_hv,hEq,hClass⟩ := hGerm y t ht
  have hOp := L16Aux.linearOp_congr_open_sets
    (Q := chartTarget y ×ˢ Set.Ioi 0) (R := Q) (p := (chartPt y y,t))
    ((isOpen_extChartAt_target (I := ComplexModel n) y).prod isOpen_Ioi) hQ
    (scalarHeatChartCoeff g y) (fun _ _ => 0) ⟨mem_extChartAt_target y,ht⟩ hpQ hEq
  have hzero := hOp.trans hClass
  rw [scalarHeat_chart_linearOp_residual g hu y ht] at hzero
  exact sub_eq_zero.mp hzero

end Yau.LeafProofs.L19Aux
