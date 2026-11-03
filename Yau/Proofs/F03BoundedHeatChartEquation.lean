import Yau.Proofs.F03ParabolicDomainTransport

/-! The original bounded-source heat satisfies the literal closed-slab chart operator in its positive-time interior. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Parabolic HeatConcreteBindings HeatTargetCandidates LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletMinimalBoundedHeat_chart_equation
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (f : M.Carrier → ℝ) (hf : AEStronglyMeasurable f μ)
    (B : ℝ) (hB : 0 < B) (hBound : ∀ y,|f y| ≤ B)
    (a : M.Carrier) (V : Set (ComplexVector n)) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVt : closure V ⊆ chartTarget a) (S : ℝ)
    (p : Point n) (hp : p ∈ V ×ˢ Ioo (0 : ℝ) S) :
    linearOp (V ×ˢ Icc (0 : ℝ) S) (scalarHeatChartCoeff g a) (fun _ _ => 0)
      (fun q : Point n => boundedKernelEvolution μ (dirichletMinimalKernelCandidate g hK μ hμ O hO)
        f q.2 (chartInv a q.1)) p=0 := by
  let l := p.2/2
  let r := p.2+1
  have hl : 0 < l := half_pos hp.2.1
  have hpLocal : p ∈ V ×ˢ Ioo l r :=
    ⟨hp.1,half_lt_self hp.2.1,by dsimp [r];linarith⟩
  have hClosed : V ×ˢ Icc (0 : ℝ) S ∈ 𝓝 p :=
    Filter.mem_of_superset ((hV.prod isOpen_Ioo).mem_nhds hp)
      (fun q hq => ⟨hq.1,hq.2.1.le,hq.2.2.le⟩)
  have hGerm : (fun q : Point n => boundedKernelEvolution μ
      (dirichletMinimalKernelCandidate g hK μ hμ O hO) f q.2 (chartInv a q.1)) =ᶠ[𝓝 p]
      dirichletMinimalBoundedHeatChart g hK μ hμ O hO f a := by
    have hPos : ∀ᶠ q : Point n in 𝓝 p,0 < q.2 :=
      continuous_snd.continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds hp.2.1)
    filter_upwards [hPos] with q hq
    exact if_neg hq.ne'
  have hOp := linearOp_congr_of_mem_nhds (scalarHeatChartCoeff g a) (fun _ _ => 0)
    hClosed ((hV.prod isOpen_Ioo).mem_nhds hpLocal) hGerm
  exact hOp.trans ((dirichletMinimalBoundedHeatChart_smooth_caloric g hK μ hμ O hO f hf B hB hBound
    a V hV hVc hVt l r hl).2 p hpLocal)

end Yau.Proofs.F03Aux
