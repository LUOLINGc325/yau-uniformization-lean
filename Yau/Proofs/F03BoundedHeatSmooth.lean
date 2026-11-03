import Yau.Proofs.F03BoundedHeatLocalLimit

/-! Joint smoothness of the same original bounded-source kernel integral at positive times. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletMinimalBoundedHeat_smooth
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ y,|f y| ≤ B) :
    SmoothSpaceTime (fun x t => boundedKernelEvolution μ
      (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t x) (Ioi 0) := by
  intro a
  apply contDiffOn_of_locally_contDiffOn
  intro p hp
  obtain ⟨V,hV,hpV,hVt,hVc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (isOpen_extChartAt_target (I := ComplexModel n) a) (singleton_subset_iff.mpr hp.1)
  let l := p.2/2
  let r := p.2+1
  have hl : 0 < l := half_pos hp.2
  have hpl : l < p.2 := half_lt_self hp.2
  have hpr : p.2 < r := by dsimp [r];linarith
  have hLocal := dirichletMinimalBoundedHeatChart_smooth_caloric g hK μ hμ O hO f hf B hB hBound
    a V hV hVc hVt l r hl
  have hActual : ContDiffOn ℝ ∞
      (fun q : Point n => boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO)
        f q.2 (chartInv a q.1)) (V ×ˢ Ioo l r) := by
    apply hLocal.1.congr
    intro q hq
    exact if_neg (hl.trans hq.2.1).ne'
  exact ⟨V ×ˢ Ioo l r,hV.prod isOpen_Ioo,⟨hpV (mem_singleton _),hpl,hpr⟩,
    hActual.mono inter_subset_right⟩

end Yau.Proofs.F03Aux
