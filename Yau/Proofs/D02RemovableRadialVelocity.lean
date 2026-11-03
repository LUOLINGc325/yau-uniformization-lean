import Yau.Proofs.D02RemovablePolar

open scoped Manifold Topology ContDiff
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

def radialPath (f : ℂ → M.Carrier) (θ : ℝ) (r : ℝ) : M.Carrier := f (polarPoint r θ)

theorem polarPoint_hasDerivAt (θ r : ℝ) :
    HasDerivAt (fun s ↦ polarPoint s θ) (polarPoint 1 θ) r := by
  simpa [polarPoint_eq_exp] using
    (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (Complex.exp (θ * Complex.I))

theorem polarPoint_contDiff (θ : ℝ) : ContDiff ℝ ∞ (fun r ↦ polarPoint r θ) := by
  simp only [polarPoint_eq_exp]
  exact Complex.ofRealCLM.contDiff.mul contDiff_const

theorem radialPath_chart_contDiffAt {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun s ↦ chartPt (radialPath f θ r) (radialPath f θ s)) r := by
  have hz : polarPoint r θ ∈ puncturedUnitDisc := by
    change 0 < ‖polarPoint r θ‖ ∧ ‖polarPoint r θ‖ < 1
    rw [polarPoint_norm, abs_of_pos hr.1]
    exact hr
  have hD := puncturedCoordinateDomain_isOpen f hf (f (polarPoint r θ))
  have hc := complex_holomorphic_contDiffOn hD
    (puncturedCoordinate_differentiableOn f hf (f (polarPoint r θ)))
  have hzD : polarPoint r θ ∈ puncturedCoordinateDomain f (f (polarPoint r θ)) :=
    ⟨hz, mem_extChartAt_source _⟩
  change ContDiffAt ℝ ∞ ((chartPt (f (polarPoint r θ)) ∘ f) ∘ (fun s ↦ polarPoint s θ)) r
  exact ((hc.contDiffAt (hD.mem_nhds hzD)).restrict_scalars ℝ).comp r
    (polarPoint_contDiff θ).contDiffAt

theorem radialPath_continuousAt {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : ContinuousAt (radialPath f θ) r := by
  have hz : polarPoint r θ ∈ puncturedUnitDisc := by
    change 0 < ‖polarPoint r θ‖ ∧ ‖polarPoint r θ‖ < 1
    rw [polarPoint_norm, abs_of_pos hr.1]
    exact hr
  change ContinuousAt (f ∘ (fun s ↦ polarPoint s θ)) r
  exact (hf.continuousOn.continuousAt
    (Yau.Proofs.B01Aux.puncturedUnitDisc_isOpen.mem_nhds hz)).comp (f := fun s : ℝ ↦ polarPoint s θ)
      (polarPoint_contDiff θ).continuous.continuousAt

theorem radialPath_contMDiffAt_real {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (radialPath f θ) r := by
  letI := L12Aux.manifold_realSmooth M
  rw [contMDiffAt_iff]
  refine ⟨radialPath_continuousAt hf θ hr, ?_⟩
  simp only [L12Aux.real_extChartAt_eq, mfld_simps, contDiffWithinAt_univ]
  exact (radialPath_chart_contDiffAt hf θ hr).of_le (by simp)

/-- The genuine real radial velocity is the original physical complex
curve derivative multiplied by the SAME unit ray direction. -/
theorem radialPath_velocity {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    L12Aux.realTangentEquiv (radialPath f θ r) (L12Aux.realCurveVelocity (radialPath f θ) r) =
      polarPoint 1 θ • physicalCurveDerivative f (polarPoint r θ) := by
  have hz : polarPoint r θ ∈ puncturedUnitDisc := by
    change 0 < ‖polarPoint r θ‖ ∧ ‖polarPoint r θ‖ < 1
    rw [polarPoint_norm, abs_of_pos hr.1]
    exact hr
  have hD := puncturedCoordinateDomain_isOpen f hf (f (polarPoint r θ))
  have hc := complex_holomorphic_contDiffOn hD
    (puncturedCoordinate_differentiableOn f hf (f (polarPoint r θ)))
  have hzD : polarPoint r θ ∈ puncturedCoordinateDomain f (f (polarPoint r θ)) :=
    ⟨hz, mem_extChartAt_source _⟩
  have hd := ((hc.contDiffAt (hD.mem_nhds hzD)).differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ
  have hdcomp := hd.comp_hasDerivAt r (polarPoint_hasDerivAt θ r)
  rw [L12Aux.realCurveVelocity_chart (radialPath_continuousAt hf θ hr)
    ((radialPath_chart_contDiffAt hf θ hr).differentiableAt (by simp)), fderiv_apply_one_eq_deriv]
  change (tangentSpaceCastModel (ComplexModel n) (f (polarPoint r θ))).symm
    (deriv ((chartPt (f (polarPoint r θ)) ∘ f) ∘ (fun s ↦ polarPoint s θ)) r) = _
  rw [hdcomp.deriv]
  have hcoords := puncturedCoordinate_fderiv_apply f hf (f (polarPoint r θ)) hzD
  rw [← L12Aux.chartVec_self]
  have hlin : fderiv ℂ (chartPt (f (polarPoint r θ)) ∘ f) (polarPoint r θ) (polarPoint 1 θ) =
      polarPoint 1 θ • fderiv ℂ (chartPt (f (polarPoint r θ)) ∘ f) (polarPoint r θ) 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (fderiv ℂ (chartPt (f (polarPoint r θ)) ∘ f) (polarPoint r θ)).map_smul (polarPoint 1 θ) (1 : ℂ)
  change chartVec (f (polarPoint r θ)) (f (polarPoint r θ))
    (fderiv ℂ (chartPt (f (polarPoint r θ)) ∘ f) (polarPoint r θ) (polarPoint 1 θ)) = _
  rw [hlin, chartVec_smul, hcoords,
    chartVec_tangentCoords _ _ (mem_extChartAt_source (f (polarPoint r θ)))]
  rfl

theorem radialPath_speed (g : HermitianField M) {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (radialPath f θ r)
    ‖L12Aux.realCurveVelocity (radialPath f θ) r‖ =
      Real.sqrt (2 * hermitianNormSq (g (f (polarPoint r θ)))
        (physicalCurveDerivative f (polarPoint r θ))) := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup g (radialPath f θ r)
  rw [L12Aux.underlyingRealTangent_norm, radialPath_velocity hf θ hr, G01Aux.hermitianNormSq_smul]
  have hunit : Complex.normSq (polarPoint 1 θ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, polarPoint_norm]
    norm_num
  rw [hunit, one_mul]
  rfl

end Yau.NodeProofs.D02RemovableAux
