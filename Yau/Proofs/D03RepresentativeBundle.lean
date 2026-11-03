import Yau.Proofs.D03RepresentativeGluing
import Yau.Proofs.B01Forms
import Yau.Proofs.B01Volume
import Yau.LeafProofs.L14CoefficientTransitions

set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Filter Set Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.D03Aux
open Yau Yau.BundleDbar Yau.Blueprint.BundlePresentation
open Yau.LeafProofs.L14Aux

private theorem complexVector_continuousSMul (n : ℕ) :
    ContinuousSMul ℂ (ComplexVector n) := by
  constructor
  change Continuous (fun p : ℂ × ComplexVector n =>
    WithLp.toLp 2 (fun i : Fin n => p.1 * p.2 i))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
    (continuous_pi fun i => continuous_fst.mul
      ((PiLp.proj 2 (fun _ : Fin n => ℂ) (𝕜 := ℂ) i).continuous.comp continuous_snd))

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The true coordinate map of the top-form fibre is injective. -/
theorem topForm_eq_of_coefficients_at_chart
    (u v : NQForm E 0) (a x : M.Carrier)
    (hx : x ∈ bundleChartSource (r := r) E a)
    (hcoeff : coefficients (r := r) E u a (chartPt a x) Fin.elim0 =
      coefficients (r := r) E v a (chartPt a x) Fin.elim0) : u x = v x := by
  have hix : chartInv a (chartPt a x) = x :=
    Yau.LeafProofs.chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hx.1)
  have hz : chartPt a x ∈ localDomain (r := r) E a := by
    refine ⟨(extChartAt (ComplexModel 1) a).map_source hx.1, ?_⟩
    change chartInv a (chartPt a x) ∈ (localTriv (r := r) E a).baseSet
    rw [hix]
    exact hx.2
  have heq : u (chartInv a (chartPt a x)) = v (chartInv a (chartPt a x)) := by
    let L := topTensorCoordinatesEquiv (r := r) E a (chartInv a (chartPt a x))
      ⟨(extChartAt (ComplexModel 1) a).map_target hz.1, hz.2⟩
    apply L.injective
    have hu : L (u (chartInv a (chartPt a x))) =
        coefficients (r := r) E u a (chartPt a x) Fin.elim0 :=
      topTensorCoordinatesEquiv_form E u a _ hz
    have hv : L (v (chartInv a (chartPt a x))) =
        coefficients (r := r) E v a (chartPt a x) Fin.elim0 :=
      topTensorCoordinatesEquiv_form E v a _ hz
    exact hu.trans (hcoeff.trans hv.symm)
  exact hix ▸ heq

/-- Holomorphy of a local top form in every overlapping original frame.
The actual determinant factor in the top-form transition is retained. -/
theorem topFormPushforward_holomorphic_at
    (hE : Holomorphic (r := r) E) (a b : M.Carrier)
    (F : ComplexVector 1 → ComplexVector r)
    (hF : DifferentiableOn ℂ F (localDomain (r := r) E a))
    (z : ComplexVector 1) (hz : z ∈ localDomain (r := r) E b)
    (hya : chartInv b z ∈ bundleChartSource (r := r) E a) :
    DifferentiableAt ℂ
      (fun w => coefficients (r := r) E (topFormPushforward (r := r) E a F) b w Fin.elim0) z := by
  have hT := (Yau.LeafProofs.L18Aux.chartTransition_contDiffAt b a hz.1 hya.1).differentiableAt (by simp)
  have hzA : chartPt a (chartInv b z) ∈ localDomain (r := r) E a := by
    refine ⟨(extChartAt (ComplexModel 1) a).map_source hya.1, ?_⟩
    change chartInv a (chartPt a (chartInv b z)) ∈ (localTriv (r := r) E a).baseSet
    rw [Yau.LeafProofs.chartInv_chartPt_of_mem a _ (by simpa only [extChartAt_source] using hya.1)]
    exact hya.2
  have hFa := (hF _ hzA).differentiableAt ((localDomain_isOpen (r := r) E a).mem_nhds hzA)
  have hP := (topBundleTransition_contDiffAt (r := r) E hE a b z hz hya).differentiableAt (by simp)
  have hPF := hP.clm_apply (hFa.comp z hT)
  have hi := continuousAt_extChartAt_symm'' (I := ComplexModel 1) hz.1
  have heq : (fun w => coefficients (r := r) E (topFormPushforward (r := r) E a F) b w Fin.elim0)
      =ᶠ[𝓝 z] (fun w => topBundleTransition (r := r) E a b w (F (chartPt a (chartInv b w)))) := by
    filter_upwards [(localDomain_isOpen (r := r) E b).mem_nhds hz,
      hi.tendsto.eventually ((bundleChartSource_isOpen (r := r) E a).mem_nhds hya)] with w hw hwa
    exact topFormPushforward_coefficients_inChart E a b F w hw hwa
  exact hPF.congr_of_eventuallyEq heq

/-- Local representative equality transfers to the original base measure by
the accepted chart-volume law. No bundle norm or metric is replaced. -/
theorem topFormPushforward_ae_eq_on_source
    (g : HermitianField M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g μ)
    (W : NQForm E 0) (a : M.Carrier) (F : ComplexVector 1 → ComplexVector r)
    (hF : F =ᵐ[(Yau.lebesgueC 1).restrict (localDomain (r := r) E a)]
      (fun z => coefficients (r := r) E W a z Fin.elim0)) :
    ∀ᵐ x ∂μ, x ∈ bundleChartSource (r := r) E a →
      topFormPushforward (r := r) E a F x = W x := by
  have hchart : ∀ᵐ z ∂(Yau.lebesgueC 1).restrict (localDomain (r := r) E a),
      topFormPushforward (r := r) E a F (chartInv a z) = W (chartInv a z) := by
    filter_upwards [hF, ae_restrict_mem (localDomain_isOpen (r := r) E a).measurableSet] with z heq hz
    let L := topTensorCoordinatesEquiv (r := r) E a (chartInv a z)
      ⟨(extChartAt (ComplexModel 1) a).map_target hz.1, hz.2⟩
    apply L.injective
    have hL1 : L (topFormPushforward (r := r) E a F (chartInv a z)) = F z :=
      (topTensorCoordinatesEquiv_form E (topFormPushforward (r := r) E a F) a z hz).trans
        (topFormPushforward_coefficients E a F z hz)
    have hL2 : L (W (chartInv a z)) = coefficients (r := r) E W a z Fin.elim0 :=
      topTensorCoordinatesEquiv_form E W a z hz
    exact hL1.trans (heq.trans hL2.symm)
  have hbase := (chartPtExtension_quasiMeasurePreserving (r := r) E g μ hμ a).ae hchart
  have hlocal : ∀ᵐ x ∂μ.restrict (bundleChartSource (r := r) E a),
      topFormPushforward (r := r) E a F x = W x := by
    filter_upwards [hbase, ae_restrict_mem (bundleChartSource_isOpen (r := r) E a).measurableSet]
      with x hx hxdom
    change topFormPushforward (r := r) E a F (chartInv a (chartPtExtension a x)) =
      W (chartInv a (chartPtExtension a x)) at hx
    rw [chartPtExtension, if_pos hxdom.1,
      Yau.LeafProofs.chartInv_chartPt_of_mem a x (by simpa only [extChartAt_source] using hxdom.1)] at hx
    exact hx
  exact (ae_restrict_iff' (bundleChartSource_isOpen (r := r) E a).measurableSet).mp hlocal

/-- Holomorphic local pushforwards of the same rough top form agree pointwise
on their genuine bundle-chart overlaps. -/
theorem holomorphic_pushforwards_eq_on_overlap
    (hE : Holomorphic (r := r) E) (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (W : NQForm E 0) (a b : M.Carrier)
    (F G : ComplexVector 1 → ComplexVector r)
    (hF : DifferentiableOn ℂ F (localDomain (r := r) E a))
    (hG : DifferentiableOn ℂ G (localDomain (r := r) E b))
    (hFW : F =ᵐ[(Yau.lebesgueC 1).restrict (localDomain (r := r) E a)]
      (fun z => coefficients (r := r) E W a z Fin.elim0))
    (hGW : G =ᵐ[(Yau.lebesgueC 1).restrict (localDomain (r := r) E b)]
      (fun z => coefficients (r := r) E W b z Fin.elim0))
    (x : M.Carrier) (hxA : x ∈ bundleChartSource (r := r) E a)
    (hxB : x ∈ bundleChartSource (r := r) E b) :
    topFormPushforward (r := r) E a F x = topFormPushforward (r := r) E b G x := by
  have : ContinuousSMul ℂ (ComplexVector 1) := complexVector_continuousSMul 1
  have : ContinuousSMul ℂ (ComplexVector r) := complexVector_continuousSMul r
  have : (Yau.lebesgueC 1).IsOpenPosMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  let Ta := topFormPushforward (r := r) E a F
  let Tb := topFormPushforward (r := r) E b G
  let V := bundleChartOverlap (r := r) E a b
  have hVo : IsOpen V := bundleChartOverlap_isOpen (r := r) E a b
  have hTa := topFormPushforward_ae_eq_on_source E g.form μ hμ W a F hFW
  have hTb := topFormPushforward_ae_eq_on_source E g.form μ hμ W b G hGW
  have hAa := ae_chartInv_of_ae (r := r) E g μ hμ b _ hTa
  have hBa := ae_chartInv_of_ae (r := r) E g μ hμ b _ hTb
  have hAE : (fun z => coefficients (r := r) E Ta b z Fin.elim0) =ᵐ[
      (Yau.lebesgueC 1).restrict V] (fun z => coefficients (r := r) E Tb b z Fin.elim0) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (show V ⊆ localDomain (r := r) E b from inter_subset_left) hAa,
      ae_restrict_of_ae_restrict_of_subset (show V ⊆ localDomain (r := r) E b from inter_subset_left) hBa,
      ae_restrict_mem hVo.measurableSet] with z hza hzb hz
    have hyb : chartInv b z ∈ bundleChartSource (r := r) E b :=
      ⟨(extChartAt (ComplexModel 1) b).map_target hz.1.1, hz.1.2⟩
    have heq : Ta (chartInv b z) = Tb (chartInv b z) := (hza hz.2).trans (hzb hyb).symm
    unfold coefficients
    rw [heq]
  have hTaHol : DifferentiableOn ℂ
      (fun z => coefficients (r := r) E Ta b z Fin.elim0) V := by
    intro z hz
    exact (topFormPushforward_holomorphic_at E hE a b F hF z hz.1 hz.2).differentiableWithinAt
  have hTbHol : DifferentiableOn ℂ
      (fun z => coefficients (r := r) E Tb b z Fin.elim0) V := by
    intro z hz
    exact (topFormPushforward_holomorphic_at E hE b b G hG z hz.1
      ⟨(extChartAt (ComplexModel 1) b).map_target hz.1.1, hz.1.2⟩).differentiableWithinAt
  have hTaCont : ContinuousOn (fun z : ComplexVector 1 => coefficients (r := r) E Ta b z Fin.elim0) V := by
    intro z hz
    exact (topFormPushforward_holomorphic_at E hE a b F hF z hz.1 hz.2).continuousAt.continuousWithinAt
  have hTbCont : ContinuousOn (fun z : ComplexVector 1 => coefficients (r := r) E Tb b z Fin.elim0) V := by
    intro z hz
    exact (topFormPushforward_holomorphic_at E hE b b G hG z hz.1
      ⟨(extChartAt (ComplexModel 1) b).map_target hz.1.1, hz.1.2⟩).continuousAt.continuousWithinAt
  have heqCoeffs := Measure.eqOn_open_of_ae_eq hAE hVo hTaCont hTbCont
  have hix : chartInv b (chartPt b x) = x :=
    Yau.LeafProofs.chartInv_chartPt_of_mem b x (by simpa only [extChartAt_source] using hxB.1)
  have hzB : chartPt b x ∈ localDomain (r := r) E b := by
    refine ⟨(extChartAt (ComplexModel 1) b).map_source hxB.1, ?_⟩
    change chartInv b (chartPt b x) ∈ (localTriv (r := r) E b).baseSet
    rw [hix]
    exact hxB.2
  have hzV : chartPt b x ∈ V := by
    refine ⟨hzB, ?_⟩
    change chartInv b (chartPt b x) ∈ bundleChartSource (r := r) E a
    rw [hix]
    exact hxA
  exact topForm_eq_of_coefficients_at_chart E Ta Tb b x hxB (heqCoeffs hzV)

/-- Glue the actual weak top form's holomorphic coefficient representatives
into an original bundle top form. Its local coefficient a.e. equality is
independent of the auxiliary complete metric used to compare overlaps. -/
theorem exists_holomorphic_topForm_representative
    (hE : Holomorphic (r := r) E) (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (W : NQForm E 0) (hW : WeakDbar (r := r) E W 0) :
    ∃ U : NQForm E 0, HolomorphicTopForm (r := r) E U ∧
      ∀ a : M.Carrier,
        (fun z => coefficients (r := r) E U a z Fin.elim0) =ᵐ[
          (Yau.lebesgueC 1).restrict (localDomain (r := r) E a)]
          (fun z => coefficients (r := r) E W a z Fin.elim0) := by
  classical
  choose F hF hFW using fun a : M.Carrier => exists_holomorphic_top_coefficients E W hW a
  let U : NQForm E 0 := fun x => topFormPushforward (r := r) E x (F x) x
  have hself (x : M.Carrier) : x ∈ bundleChartSource (r := r) E x :=
    ⟨mem_extChartAt_source x, FiberBundle.mem_baseSet_trivializationAt' x⟩
  have hUloc (a x : M.Carrier) (hx : x ∈ bundleChartSource (r := r) E a) :
      U x = topFormPushforward (r := r) E a (F a) x :=
    holomorphic_pushforwards_eq_on_overlap E hE g μ hμ W x a (F x) (F a)
      (hF x) (hF a) (hFW x) (hFW a) x (hself x) hx
  have hUcoeff (a : M.Carrier) : EqOn
      (fun z => coefficients (r := r) E U a z Fin.elim0) (F a)
      (localDomain (r := r) E a) := by
    intro z hz
    have hloc := hUloc a (chartInv a z)
      ⟨(extChartAt (ComplexModel 1) a).map_target hz.1, hz.2⟩
    calc
      coefficients (r := r) E U a z Fin.elim0 =
          coefficients (r := r) E (topFormPushforward (r := r) E a (F a)) a z Fin.elim0 := by
        unfold coefficients
        rw [hloc]
      _ = F a z := topFormPushforward_coefficients E a (F a) z hz
  refine ⟨U, ?_, ?_⟩
  · intro a α
    exact (differentiableOn_piLp 2).mp ((hF a).congr (hUcoeff a)) α
  · intro a
    have heq : (fun z => coefficients (r := r) E U a z Fin.elim0) =ᵐ[
        (Yau.lebesgueC 1).restrict (localDomain (r := r) E a)] F a := by
      filter_upwards [ae_restrict_mem (localDomain_isOpen (r := r) E a).measurableSet] with z hz
      exact hUcoeff a hz
    exact heq.trans (hFW a)

/-- Equality of original top-form coefficients almost everywhere gives equality
for the exact ordinary disc area measure. The factor two in the real volume
normalization is cancelled only as a nonzero measure scalar. -/
theorem topForms_ae_eq_discArea_of_coefficients_ae_eq
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (U W : NQForm E 0)
    (hcoeff : ∀ a : M.Carrier,
      (fun z => coefficients (r := r) E U a z Fin.elim0) =ᵐ[
        (Yau.lebesgueC 1).restrict (localDomain (r := r) E a)]
        (fun z => coefficients (r := r) E W a z Fin.elim0)) :
    ∀ᵐ x ∂Yau.Blueprint.BundlePresentation.discArea c, U x = W x := by
  have ht : ∀ᵐ x ∂((2 : ℝ≥0∞) • Yau.Blueprint.BundlePresentation.discArea c), U x = W x := by
    apply ae_of_bundleCharts (r := r) E (B01Aux.flatDiscField c hc)
      ((2 : ℝ≥0∞) • Yau.Blueprint.BundlePresentation.discArea c) (B01Aux.flatDiscField_volume c hc) _
    intro a
    filter_upwards [hcoeff a,
      ae_restrict_mem (localDomain_isOpen (r := r) E a).measurableSet] with z heq hz
    let L := topTensorCoordinatesEquiv (r := r) E a (chartInv a z)
      ⟨(extChartAt (ComplexModel 1) a).map_target hz.1, hz.2⟩
    apply L.injective
    have hL1 : L (U (chartInv a z)) = coefficients (r := r) E U a z Fin.elim0 :=
      topTensorCoordinatesEquiv_form E U a z hz
    have hL2 : L (W (chartInv a z)) = coefficients (r := r) E W a z Fin.elim0 :=
      topTensorCoordinatesEquiv_form E W a z hz
    exact hL1.trans (heq.trans hL2.symm)
  exact (Measure.ae_ennreal_smul_measure_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp ht

/-- The local coefficient formula of the actual intrinsic tensor s dz. -/
theorem sectionTopForm_coefficients
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (s : Section E)
    (a : M.Carrier) (z : ComplexVector 1) (hz : z ∈ localDomain (r := r) E a) :
    coefficients (r := r) E (B01Aux.sectionTopForm E c s) a z Fin.elim0 =
      wirt (fun w => c (chartInv a w)) z (stdVec 0) •
        sectionCoefficients (r := r) E s a z := by
  unfold coefficients
  rw [B01Aux.sectionTopForm_spec E c s, map_smul]
  change _ • sectionCoefficients (r := r) E s a z = _
  rw [wirt_eq_fderiv_of_complex_differentiable _ z (stdVec 0)
    ((B01Aux.disc_inChart_contDiffAt c hc a hz.1).differentiableAt (by simp)),
    B01Aux.disc_inChart_fderiv c hc a hz.1]

/-- The coordinate derivative never vanishes on a valid local chart. -/
theorem disc_chart_wirt_ne_zero
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (a : M.Carrier) (z : ComplexVector 1) (hz : z ∈ chartTarget a) :
    wirt (fun w => c (chartInv a w)) z (stdVec 0) ≠ 0 := by
  have hd := Yau.LeafProofs.L18Aux.hMat_det_re_pos (B01Aux.flatDiscField c hc) a hz
  rw [B01Aux.flatDiscField_hMat_det c hc a hz] at hd
  intro hzero
  simpa [hzero] using hd

/-- Holomorphy of the actual nonvanishing coordinate Jacobian. -/
theorem disc_chart_wirt_differentiableOn
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (a : M.Carrier) :
    DifferentiableOn ℂ
      (fun z => wirt (fun w => c (chartInv a w)) z (stdVec 0)) (chartTarget a) := by
  intro z hz
  have hC := B01Aux.disc_inChart_contDiffAt c hc a hz
  have hD := (hC.fderiv_right (m := ∞) (by simp)).clm_apply
    (show ContDiffAt ℂ ∞ (fun _ : ComplexVector 1 => stdVec 0) z from contDiffAt_const)
  have heq : (fun w => wirt (fun u => c (chartInv a u)) w (stdVec 0)) =ᶠ[𝓝 z]
      (fun w => fderiv ℂ (fun u => c (chartInv a u)) w (stdVec 0)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel 1) a).mem_nhds hz] with w hw
    exact wirt_eq_fderiv_of_complex_differentiable _ w (stdVec 0)
      ((B01Aux.disc_inChart_contDiffAt c hc a hw).differentiableAt (by simp))
  exact ((hD.differentiableAt (by simp)).congr_of_eventuallyEq heq).differentiableWithinAt

/-- Genuine original-bundle weak-to-holomorphic regularity with the exact
ordinary area a.e. relation. The arbitrary weak representative is retained. -/
theorem exists_holomorphic_section_of_weak_closed_top
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (hE : Holomorphic (r := r) E) (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (W : NQForm E 0) (hW : WeakDbar (r := r) E W 0) :
    ∃ b : Section E, HolomorphicSection (r := r) E b ∧
      (∀ᵐ x ∂Yau.Blueprint.BundlePresentation.discArea c, B01Aux.sectionTopForm E c b x = W x) := by
  obtain ⟨U, hUHol, hUcoeff⟩ := exists_holomorphic_topForm_representative E hE g μ hμ W hW
  obtain ⟨b, hb, _⟩ := B01Aux.topFormSectionRecovery E c hc U
  have hUEq : U = B01Aux.sectionTopForm E c b := by
    funext x
    apply Subtype.ext
    ext v w
    exact hb x v w
  have hbHol : HolomorphicSection (r := r) E b := by
    intro a
    let J : ComplexVector 1 → ℂ := fun z => wirt (fun w => c (chartInv a w)) z (stdVec 0)
    have hJD : DifferentiableOn ℂ J (localDomain (r := r) E a) :=
      (disc_chart_wirt_differentiableOn c hc a).mono inter_subset_left
    have hJne : ∀ z ∈ localDomain (r := r) E a, J z ≠ 0 :=
      fun z hz => disc_chart_wirt_ne_zero c hc a z hz.1
    have hUC : DifferentiableOn ℂ
        (fun z => coefficients (r := r) E U a z Fin.elim0) (localDomain (r := r) E a) :=
      (differentiableOn_piLp 2).mpr (hUHol a)
    have hproduct := (hJD.inv hJne).smul hUC
    apply hproduct.congr
    intro z hz
    change sectionCoefficients (r := r) E b a z =
      (J z)⁻¹ • coefficients (r := r) E U a z Fin.elim0
    rw [hUEq, sectionTopForm_coefficients E c hc b a z hz]
    change sectionCoefficients (r := r) E b a z = (J z)⁻¹ • (J z • _)
    rw [smul_smul, inv_mul_cancel₀ (hJne z hz), one_smul]
  refine ⟨b, hbHol, ?_⟩
  have harea := topForms_ae_eq_discArea_of_coefficients_ae_eq E c hc U W hUcoeff
  simpa only [hUEq] using harea

end Yau.Proofs.D03Aux
