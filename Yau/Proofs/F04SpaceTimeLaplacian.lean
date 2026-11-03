import Yau.Proofs.F04FlowGradientContinuity

open Filter Set
open scoped Topology ContDiff Manifold Matrix

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem closed_chart_spatial_partial_contDiffOn
    {S : ℝ} (hS : 0 < S) (c : M.Carrier)
    {F : ComplexVector n × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (chartTarget c ×ˢ Icc 0 S)) (i : RIdx n) :
    ContDiffOn ℝ ∞ (fun p => rDeriv (fun z => F (z, p.2)) p.1 i)
      (chartTarget c ×ˢ Icc 0 S) := by
  have huniq := (isOpen_extChartAt_target (I := ComplexModel n) c).uniqueDiffOn.prod
    (uniqueDiffOn_Icc hS)
  have hc := (hF.fderivWithin huniq (show ∞ + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply
    (contDiffOn_const (c := (realVec i, (0 : ℝ))))
  apply hc.congr
  intro p hp
  have hd := (hF.differentiableOn (by simp) p hp).hasFDerivWithinAt
  have hm : HasFDerivAt (fun z : ComplexVector n => (z, p.2))
      ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod (0 : ComplexVector n →L[ℝ] ℝ)) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hmaps : MapsTo (fun z : ComplexVector n => (z, p.2)) (chartTarget c)
      (chartTarget c ×ˢ Icc 0 S) := fun _ hz => ⟨hz, hp.2⟩
  have he := congrArg (fun L => L (realVec i))
    ((hd.comp p.1 hm.hasFDerivWithinAt hmaps).hasFDerivAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hp.1)).fderiv
  change fderiv ℝ (fun z => F (z, p.2)) p.1 (realVec i) = _
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply] using he

theorem closed_chart_spatial_hessian_contDiffOn
    {S : ℝ} (hS : 0 < S) (c : M.Carrier)
    {F : ComplexVector n × ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F (chartTarget c ×ˢ Icc 0 S)) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun p => fderiv ℝ (fderiv ℝ (fun z => F (z, p.2))) p.1
      (realVec i) (realVec j)) (chartTarget c ×ˢ Icc 0 S) := by
  have hj := closed_chart_spatial_partial_contDiffOn hS c hF j
  have hij := closed_chart_spatial_partial_contDiffOn hS c hj i
  apply hij.congr
  intro p hp
  have hs : ContDiffOn ℝ ∞ (fun z => F (z, p.2)) (chartTarget c) :=
    hF.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, hp.2⟩)
  exact (rDeriv_rDeriv_eq_hessian
    (((hs.contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hp.1))).of_le
      (by simp)) i j).symm

/-- The actual evolving Laplacian of a physical smooth profile is jointly
 smooth on the original closed time slab. -/
theorem metricFamily_laplacian_spaceTime_smooth
    (h : ℝ → HermitianField M) {S : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S))
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Icc 0 S)) :
    SmoothSpaceTime (fun x t => laplacian (h t) (fun y => u y t) x) (Icc 0 S) := by
  intro c
  have hi (i j : RIdx n) : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      (1 / 2 : ℝ) * (realMetricFn (h p.2) c p.1)⁻¹ i j) (chartTarget c ×ˢ Icc 0 S) :=
    contDiffOn_const.mul (contDiffOn_matrix_inv (hh c)
      (fun p hp => (Yau.LeafProofs.L12Aux.realMetricFn_posDef (h p.2) c p.1 hp.1).det_pos.ne') i j)
  have hsum : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => ∑ i, ∑ j,
      (1 / 2 : ℝ) * (realMetricFn (h p.2) c p.1)⁻¹ i j *
        fderiv ℝ (fderiv ℝ (fun z => u (chartInv c z) p.2)) p.1 (realVec i) (realVec j))
      (chartTarget c ×ˢ Icc 0 S) := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact (hi i j).mul (closed_chart_spatial_hessian_contDiffOn hS c (hu c) i j)
  apply hsum.congr
  intro p hp
  have hs : SmoothFn (fun x => u x p.2) := fun a => (hu a).comp
    (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, hp.2⟩)
  exact flowChartPrincipal_operator h c hs p.1 hp.1 p.2

end Yau.F04Proof
