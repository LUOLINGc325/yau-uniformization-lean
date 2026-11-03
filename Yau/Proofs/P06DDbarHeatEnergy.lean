import Yau.Proofs.P06DDbarHeatCalculus

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual compact dd norm is exactly one half the scalar Hodge norm. -/
theorem ddCore_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (hcf : HasCompactSupport f) :
    ‖realizeActualForm g μ (ddRealForm f) (dd_l2 g μ hμ f hf hcf)‖ ^ 2 =
      (1 / 4 : ℝ) * ‖realizeActualForm g μ (hodgeRealForm g.form 0 (scalarForm f))
        (hodgeRealForm_l2 g μ hμ _ (scalarForm_smooth f hf) (scalarForm_compact f hcf))‖ ^ 2 := by
  let τ := formTrace g.form (ddRealForm f)
  have hτ : SmoothFn τ := trace_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g)
    _ (dd_smooth f hf) (dd_properties f hf).2.1
  have hcτ : CompactlySupportedRealForm (scalarForm τ) := by
    apply (hodgeRealForm_compactlySupported g μ hμ (scalarForm f)
      (scalarForm_smooth f hf) (scalarForm_compact f hcf)).of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx hz
    apply hx
    have he := congrFun (hodge_scalar_eq_neg_two_trace_dd g hk f hf) x
    rw [hz] at he
    have he' : (-2 : ℝ) • scalarForm τ x = 0 := by
      simpa only [Pi.smul_apply] using he.symm
    exact (smul_eq_zero.mp he').resolve_left (by norm_num)
  have hcJ : CompactlySupportedRealForm (jDifferential f) :=
    WeakCurrent.jPullbackOne_compact _ (exteriorRealForm_compactlySupported _
      (scalarForm_smooth f hf) (scalarForm_compact f hcf))
  have hGreen := integral_exterior_codifferential g μ hμ (jDifferential f)
    (ddRealForm f) (jDifferential_smooth f hf) (dd_smooth f hf) hcJ
  have hδ := codifferential_closed_oneOne_eq g.form (L12Aux.metricSmooth_of_smoothMetric g)
    hk _ (dd_smooth f hf) (dd_properties f hf).2.1 (dd_properties f hf).2.2.1
  have hE := integral_hodgeRealForm_zero_energy g μ hμ (scalarForm f) (scalarForm τ)
    (scalarForm_smooth f hf) (scalarForm_smooth τ hτ) hcτ
  rw [realizeActualForm_norm_sq, realizeActualForm_norm_sq]
  calc
    (∫ x, formNormSq g.form (ddRealForm f) x ∂μ) =
        (-(1 / 2 : ℝ)) * ∫ x, formInner g.form
          (exteriorRealForm (jDifferential f)) (ddRealForm f) x ∂μ := by
      change (∫ x, formInner g.form (ddRealForm f) (ddRealForm f) x ∂μ) = _
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => congrFun
        (formInner_smul_left g.form (-(1/2 : ℝ)) (exteriorRealForm (jDifferential f)) (ddRealForm f)) x
    _ = (-(1 / 2 : ℝ)) * ∫ x, formInner g.form
        (jDifferential f) (codifferentialRealForm g.form (ddRealForm f)) x ∂μ := by rw [hGreen]
    _ = (-(1 / 2 : ℝ)) * ∫ x, formInner g.form
        (exteriorRealForm (scalarForm f)) (exteriorRealForm (scalarForm τ)) x ∂μ := by
      rw [hδ]
      simp only [jDifferential, WeakCurrent.formInner_jPullbackOne]
      rfl
    _ = (-(1 / 2 : ℝ)) * ∫ x, formInner g.form
        (hodgeRealForm g.form 0 (scalarForm f)) (scalarForm τ) x ∂μ := by rw [hE]
    _ = (1 / 4 : ℝ) * ∫ x, formNormSq g.form
        (hodgeRealForm g.form 0 (scalarForm f)) x ∂μ := by
      rw [hodge_scalar_eq_neg_two_trace_dd g hk f hf]
      simp only [formNormSq, formInner_smul_left, formInner_smul_right,
        Pi.smul_apply, smul_eq_mul, integral_const_mul]
      ring

end Yau.NodeProofs.P06Aux.DDbarHeat
