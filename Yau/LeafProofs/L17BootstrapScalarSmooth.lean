import Yau.LeafProofs.L17UniformPartition

noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapSmoothAux
open L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Local joint regularity in the actual background charts implies the original
chartwise notion on the same time set, including all of its endpoints. -/
theorem smoothSpaceTime_of_local_background_charts (P : UniformChartPartition g)
    (f : M.Carrier → ℝ → ℝ) (I : Set ℝ)
    (hLocal : ∀ y : M.Carrier, ∃ p : P.centers, ∃ z : ComplexVector n, ∃ r : ℝ,
      0<r ∧ z∈ball 0 P.radius ∧ P.charts.chart p z=y ∧
      ContDiffOn ℝ ∞ (fun a : ComplexVector n × ℝ => f (P.charts.chart p a.1) a.2)
        (ball z r ×ˢ I)) : SmoothSpaceTime f I := by
  intro c a ha
  obtain ⟨p,z,r,hr,hz,hzx,hReg⟩ := hLocal (chartInv c a.1)
  let e := P.charts.chart p
  let psi : ComplexVector n → ComplexVector n := fun w => e.symm (chartInv c w)
  let O := inverseChartDomain e c
  have hzSource : z∈e.source := P.charts.closedBall_source p
    (ball_subset_closedBall ((ball_subset_ball P.radius_lt.le) hz))
  have hTarget : chartInv c a.1∈e.target := hzx ▸ e.map_source hzSource
  have haO : a.1∈O := ⟨ha.1,hTarget⟩
  have hpsi : ContDiffOn ℝ ∞ psi O :=
    inverseChart_real_contDiffOn e (P.charts.inverse_differentiable p) c
  have hO : IsOpen O := inverseChartDomain_isOpen e c
  have hCoord : psi a.1=z := by
    change e.symm (chartInv c a.1)=z
    rw [←hzx]
    exact e.left_inv hzSource
  let V : Set (ComplexVector n) := O∩psi ⁻¹' ball z r
  have hV : IsOpen V := hpsi.continuousOn.isOpen_inter_preimage hO isOpen_ball
  have haV : a.1∈V := by
    refine ⟨haO,?_⟩
    change dist (psi a.1) z<r
    rw [hCoord,dist_self]
    exact hr
  have hMap : ContDiffOn ℝ ∞ (fun b : ComplexVector n × ℝ => (psi b.1,b.2)) (V ×ˢ I) :=
    (hpsi.comp contDiff_fst.contDiffOn (fun b hb => hb.1.1)).prodMk contDiff_snd.contDiffOn
  have hComp : ContDiffOn ℝ ∞
      (fun b : ComplexVector n × ℝ => f (e (psi b.1)) b.2) (V ×ˢ I) :=
    hReg.comp hMap (fun b hb => ⟨hb.1.2,hb.2⟩)
  have hEqual : EqOn (fun b : ComplexVector n × ℝ => f (chartInv c b.1) b.2)
      (fun b : ComplexVector n × ℝ => f (e (psi b.1)) b.2) (V ×ˢ I) := by
    intro b hb
    have hChart : e (psi b.1)=chartInv c b.1 := e.right_inv hb.1.1.2
    change f (chartInv c b.1) b.2=f (e (psi b.1)) b.2
    rw [hChart]
  have hAt := (hComp.congr hEqual) a ⟨haV,ha.2⟩
  apply hAt.mono_of_mem_nhdsWithin
  filter_upwards [mem_nhdsWithin_of_mem_nhds ((hV.prod isOpen_univ).mem_nhds
    (show a∈V ×ˢ (univ : Set ℝ) from ⟨haV,mem_univ _⟩)),
    self_mem_nhdsWithin] with b hbV hbI
  exact ⟨hbV.1,hbI.2⟩

end Yau.LeafProofs.L17BootstrapSmoothAux
