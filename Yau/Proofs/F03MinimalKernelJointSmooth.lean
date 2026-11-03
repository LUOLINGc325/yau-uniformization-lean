import Yau.Proofs.F03MinimalPackedLimit

/-! The original pointwise ciSup is jointly smooth in both points and positive time. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

theorem dirichletMinimalKernelCandidate_joint_smooth
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) :
    KernelSmoothOn univ (dirichletMinimalKernelCandidate g hK μ hμ O hO) := by
  intro x y
  apply contDiffOn_of_locally_contDiffOn
  intro p hp
  obtain ⟨Ox,hx,hzx,hxt,hxc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (isOpen_extChartAt_target (I := ComplexModel n) x) (singleton_subset_iff.mpr hp.1.1.1)
  obtain ⟨Oy,hy,hwy,hyt,hyc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (isOpen_extChartAt_target (I := ComplexModel n) y) (singleton_subset_iff.mpr hp.1.2.1)
  let l : ℝ := p.2/2
  let r : ℝ := p.2+1
  have hl : 0 < l := half_pos hp.2
  obtain ⟨_J,hSmooth,_hEq,_hLimit⟩ := dirichletMinimalPackedKernel_limit g hK μ hμ O hO x y
    Ox Oy hx hy hxc hyc hxt hyt l r hl
  let W := (Ox ×ˢ Oy) ×ˢ Ioo l r
  have hW : IsOpen W := (hx.prod hy).prod isOpen_Ioo
  have hpW : p ∈ W :=
    ⟨⟨hzx (mem_singleton _),hwy (mem_singleton _)⟩,half_lt_self hp.2,by dsimp [r];linarith⟩
  have hComp : ContDiffOn ℝ ∞
      (fun q => dirichletMinimalPackedKernel g hK μ hμ O hO x y (kernelPairTimePack n q)) W := by
    apply hSmooth.comp (kernelPairTimePack n).contDiff.contDiffOn
    intro q hq
    exact ⟨⟨q.1,hq.1,rfl⟩,hq.2⟩
  have hActual : ContDiffOn ℝ ∞
      (fun q : ((Space n × Space n) × ℝ) => dirichletMinimalKernelCandidate g hK μ hμ O hO q.2
        (chartInv x q.1.1) (chartInv y q.1.2)) W := by
    convert hComp using 1
    funext q
    simp only [dirichletMinimalPackedKernel,kernelPairTimePack,ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.refl_apply,ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨W,hW,hpW,hActual.mono inter_subset_right⟩

end Yau.Proofs.F03Aux
