import Yau.Proofs.F03BoundedHeatSmooth
import Yau.Proofs.F03DirichletClassicalEquation

/-! The same original bounded-source integral solves the actual total Laplacian equation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic HeatConcreteBindings HeatTargetCandidates LeafProofs.L19Aux LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2300000

theorem dirichletMinimalBoundedHeat_hasDerivAt
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ y,|f y| ≤ B)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => boundedKernelEvolution μ
      (dirichletMinimalKernelCandidate g hK μ hμ O hO) f s x)
      (laplacian g.form (boundedKernelEvolution μ
        (dirichletMinimalKernelCandidate g hK μ hμ O hO) f t) x) t := by
  let u : M.Carrier → ℝ → ℝ := fun y s => boundedKernelEvolution μ
    (dirichletMinimalKernelCandidate g hK μ hμ O hO) f s y
  have hSmooth : SmoothSpaceTime u (Ioi 0) :=
    dirichletMinimalBoundedHeat_smooth g hK μ hμ O hO f hf B hB hBound
  let p : Point n := (chartPt x x,t)
  obtain ⟨V,hV,hpV,hVt,hVc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (isOpen_extChartAt_target (I := ComplexModel n) x) (singleton_subset_iff.mpr (mem_extChartAt_target x))
  let l := t/2
  let r := t+1
  have hl : 0 < l := half_pos ht
  have hpD : p ∈ V ×ˢ Ioo l r :=
    ⟨hpV (mem_singleton _),half_lt_self ht,by dsimp [p,r];linarith⟩
  have hLocal := dirichletMinimalBoundedHeatChart_smooth_caloric g hK μ hμ O hO f hf B hB hBound
    x V hV hVc hVt l r hl
  have hinv : chartInv x (chartPt x x)=x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hpGlobal : p ∈ {z | z ∈ chartTarget x ∧ chartInv x z ∈ univ} ×ˢ Ioi (0 : ℝ) :=
    ⟨⟨mem_extChartAt_target x,mem_univ _⟩,ht⟩
  have hGerm : (fun q : Point n => u (chartInv x q.1) q.2) =ᶠ[𝓝 p]
      dirichletMinimalBoundedHeatChart g hK μ hμ O hO f x := by
    have hPos : ∀ᶠ q : Point n in 𝓝 p,0 < q.2 :=
      continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds ht)
    filter_upwards [hPos] with q hq
    exact if_neg hq.ne'
  have hOp := linearOp_congr_open_sets
    ((dirichletChartInterior_open univ isOpen_univ x).prod isOpen_Ioi) (hV.prod isOpen_Ioo)
    (scalarHeatChartCoeff g x) (fun _ _ => 0) hpGlobal hpD hGerm
  have hZero := hOp.trans (hLocal.2 p hpD)
  have hSmoothGlobal : ∀ a : M.Carrier,ContDiffOn ℝ ∞
      (fun q : Point n => u (chartInv a q.1) q.2)
      ({z | z ∈ chartTarget a ∧ chartInv a z ∈ univ} ×ˢ Ioi (0 : ℝ)) := by
    intro a
    simpa using hSmooth a
  rw [dirichletHeat_chart_linearOp_residual g univ isOpen_univ hSmoothGlobal x (mem_univ x) ht] at hZero
  have hc := ((hSmooth x).contDiffAt
    (((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi).mem_nhds
      (show (chartPt x x,t) ∈ chartTarget x ×ˢ Ioi (0 : ℝ) from ⟨mem_extChartAt_target x,ht⟩))).comp t
        (contDiffAt_const.prodMk contDiffAt_id)
  have hd : DifferentiableAt ℝ (u x) t := by
    simpa only [Function.comp_def,hinv] using hc.differentiableAt (by simp)
  rw [← sub_eq_zero.mp hZero]
  exact hd.hasDerivAt

end Yau.Proofs.F03Aux
