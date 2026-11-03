import Yau.Proofs.D02RemovableRadialVelocity
import Yau.Proofs.D02RemovableWeightedLine
import Yau.Proofs.D02RemovableRadialMetric

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Blueprint.V03Proof Yau.NodeProofs.D02Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

/-- Actual induced distance along one ray is bounded by its physical speed integral. -/
theorem radialPath_distance_le_integral (g : SmoothMetric M) {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    (θ : ℝ) {s t : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) (hst : s ≤ t)
    (hint : IntegrableOn (fun r ↦ Real.sqrt (2 * hermitianNormSq (g.form (f (polarPoint r θ)))
      (physicalCurveDerivative f (polarPoint r θ)))) (Icc s t) volume) :
    inducedDistance g.form (radialPath f θ s) (radialPath f θ t) ≤
      ∫ r in Icc s t, Real.sqrt (2 * hermitianNormSq (g.form (f (polarPoint r θ)))
        (physicalCurveDerivative f (polarPoint r θ))) := by
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z ↦ L12Aux.underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z ↦ L12Aux.underlyingRealTangentInnerProductSpace g.form z
  have hsub : Icc s t ⊆ Ioo (0 : ℝ) 1 := fun r hr ↦ ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (radialPath f θ) (Icc s t) :=
    fun r hr ↦ (radialPath_contMDiffAt_real hf θ (hsub hr)).contMDiffWithinAt
  have hd : ENNReal.ofReal (inducedDistance g.form (radialPath f θ s) (radialPath f θ t)) ≤
      Manifold.pathELength 𝓘(ℝ, ComplexVector n) (radialPath f θ) s t := by
    rw [L12Aux.inducedDistance_eq_riemannianEDist g]
    exact Manifold.riemannianEDist_le_pathELength hcurve rfl rfl hst
  have hlen : Manifold.pathELength 𝓘(ℝ, ComplexVector n) (radialPath f θ) s t =
      ENNReal.ofReal (∫ r in Icc s t, Real.sqrt (2 * hermitianNormSq (g.form (f (polarPoint r θ)))
        (physicalCurveDerivative f (polarPoint r θ)))) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun r ↦ Real.sqrt_nonneg _))]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro r hr
    change ‖L12Aux.realCurveVelocity (radialPath f θ) r‖ₑ = _
    rw [← ofReal_norm]
    congr 1
    exact radialPath_speed g.form hf θ (hsub hr)
  rw [hlen] at hd
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun r ↦ Real.sqrt_nonneg _))).mp hd

/-- The original weighted physical energy produces a full actual radial limit.
Completeness is the existing `SmoothMetric.complete_distance` field, through L12. -/
theorem exists_physical_radial_limit (g : SmoothMetric M) {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hσ : 0 < σ)
    (henergy : physicalWeightedEnergy g.form f ρ σ < ⊤) :
    ∃ (θ : ℝ) (p : M.Carrier), Tendsto (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp (θ * Complex.I)))
      (𝓝[>] 0) (𝓝 p) := by
  obtain ⟨θ, hθ⟩ := exists_good_physical_ray g hf hρ hρ1 hσ henergy
  let q := fun r ↦ hermitianNormSq (g.form (f (polarPoint r θ)))
    (physicalCurveDerivative f (polarPoint r θ))
  have hmap : MapsTo (fun r ↦ polarPoint r θ) (Ioo 0 ρ) puncturedUnitDisc := by
    intro r hr
    change 0 < ‖polarPoint r θ‖ ∧ ‖polarPoint r θ‖ < 1
    rw [polarPoint_norm, abs_of_pos hr.1]
    exact ⟨hr.1, hr.2.trans hρ1⟩
  have hqc : ContinuousOn q (Ioo 0 ρ) := (physicalEnergy_continuousOn g hf).comp
    (polarPoint_contDiff θ).continuous.continuousOn hmap
  have hq0 : ∀ r, 0 ≤ q r := fun r ↦ hermitianNormSq_nonneg _ _
  have hsqrt : IntegrableOn (fun r ↦ Real.sqrt (q r)) (Ioo 0 ρ) volume :=
    sqrt_integrable_of_weighted_energy hρ hσ (hqc.aestronglyMeasurable measurableSet_Ioo)
      (Eventually.of_forall hq0) hθ
  let v := fun r ↦ Real.sqrt (2 * q r)
  have hv : IntegrableOn v (Ioo 0 ρ) volume := by
    have heq : v = fun r ↦ Real.sqrt 2 * Real.sqrt (q r) := by
      funext r
      exact Real.sqrt_mul (by norm_num) _
    rw [heq]
    exact hsqrt.const_mul _
  letI := L12Aux.inducedMetricSpace g
  letI := L12Aux.inducedMetricSpace_complete g
  obtain ⟨p, hp⟩ := exists_radial_limit_of_integrable_speed hρ hv
    (fun r hr ↦ Real.sqrt_nonneg _) (γ := radialPath f θ) (by
      intro s hs t ht hst
      exact radialPath_distance_le_integral g hf θ ⟨hs.1, hs.2.trans hρ1⟩
        ⟨ht.1, ht.2.trans hρ1⟩ hst (hv.mono_set
          (fun r hr ↦ ⟨hs.1.trans_le hr.1, hr.2.trans_lt ht.2⟩)))
  refine ⟨θ, p, ?_⟩
  have heq : (fun r : ℝ ↦ f ((r : ℂ) * Complex.exp (θ * Complex.I))) = radialPath f θ := by
    funext r
    exact congrArg f (polarPoint_eq_exp r θ).symm
  rw [heq]
  exact hp

end Yau.NodeProofs.D02RemovableAux
