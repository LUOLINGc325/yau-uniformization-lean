import Yau.Proofs.P08CanonicalRegularization
import Yau.Proofs.P08CompactGreen
import Yau.Proofs.F02Regularity
import Yau.Proofs.G04

/-! Compact integration by parts for the actual regularized canonical norm.
Only compactly supported products are integrated over the whole manifold. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Matrix ComplexOrder ENNReal
namespace Yau.NodeProofs.P08Aux.ScalarAverage
open Yau Yau.Blueprint Yau.LeafProofs
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem scalarCurvature_nonneg (X : KahlerManifold n) (x : Pt X) :
    0 ≤ scalarCurvature X.metric.form x :=
  P06Aux.matrix_trace_mul_nonneg _ _
    (L12Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).inv.posSemidef
    (P06Aux.kahlerManifold_ricci_posSemidef X x)

theorem scalarCurvature_smooth (X : KahlerManifold n) :
    SmoothFn (scalarCurvature X.metric.form) :=
  Yau.Proofs.F02Aux.scalarCurvature_smooth_of_G04 G04_proved X

/-- The signed Green integral is bounded before taking any singular limit. -/
theorem regularized_cutoff_lintegral_bound (X : KahlerManifold n) (o : Pt X)
    (S : CanonicalSection X.manifold) (hS : IsHolomorphicCanonical S)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    {ε R K : ℝ} (hε : 0 < ε) (hR : 0 < R) (hK : 0 ≤ K)
    {χ : Pt X → ℝ} (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχs : tsupport χ ⊆ distBall X.metric.form o R)
    (hχlap : ∀ x, |laplacian X.metric.form χ x| ≤ K) :
    (∫⁻ x, ENNReal.ofReal (χ x *
        (canonicalNormSq X.metric.form S x / (canonicalNormSq X.metric.form S x + ε) *
          scalarCurvature X.metric.form x)) ∂μ) ≤
      ENNReal.ofReal K * ∫⁻ x in distBall X.metric.form o R,
        ENNReal.ofReal |Real.log (canonicalNormSq X.metric.form S x + ε)| ∂μ := by
  let q := canonicalNormSq X.metric.form S
  let w := fun x => Real.log (q x + ε)
  let f := fun x => χ x * (q x / (q x + ε) * scalarCurvature X.metric.form x)
  have hw : SmoothFn w := canonical_regularized_log_smooth X.metric S hS hε
  obtain ⟨hχw, hwχ, hswap⟩ :=
    integral_laplacian_compact_swap X.metric X.kahler_metric μ hμ hw hχ hcχ
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (hχ0 x)
    (canonical_regularized_laplacian_lower X S hS hε x).1
  have hfΔ : ∀ x, f x ≤ χ x * laplacian X.metric.form w x := fun x =>
    mul_le_mul_of_nonneg_left (canonical_regularized_laplacian_lower X S hS hε x).2 (hχ0 x)
  have hqm := (L18Aux.continuous_of_smoothFn
    (Yau.Proofs.P04Aux.canonicalNormSq_smooth X.metric S hS)).measurable
  have hfm : Measurable f := (L18Aux.continuous_of_smoothFn hχ).measurable.mul
    ((hqm.div (hqm.add measurable_const)).mul
      (L18Aux.continuous_of_smoothFn (scalarCurvature_smooth X)).measurable)
  have hfi : Integrable f μ := hχw.mono' hfm.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfΔ x)
  have habs : IntegrableOn (fun x => |w x|) (distBall X.metric.form o R) μ :=
    (L18Aux.smoothFn_integrableOn_distBall X.metric μ hμ hw o hR).abs
  have hu : (∫ x, w x * laplacian X.metric.form χ x ∂μ) ≤
      K * ∫ x in distBall X.metric.form o R, |w x| ∂μ := by
    have heq : (∫ x in distBall X.metric.form o R, w x * laplacian X.metric.form χ x ∂μ) =
        ∫ x, w x * laplacian X.metric.form χ x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [L19Aux.laplacian_zero_of_notMem_tsupport X.metric.form hχ
        (fun h => hx (hχs h)), mul_zero]
    rw [← heq, ← integral_const_mul]
    apply setIntegral_mono_on hwχ.integrableOn (habs.const_mul K)
      (L12Aux.isOpen_distBall X.metric o R).measurableSet
    intro x _
    calc
      w x * laplacian X.metric.form χ x ≤ |w x * laplacian X.metric.form χ x| := le_abs_self _
      _ = |w x| * |laplacian X.metric.form χ x| := abs_mul _ _
      _ ≤ K * |w x| := by nlinarith [hχlap x, abs_nonneg (w x)]
  have hb : (∫ x, f x ∂μ) ≤ K * ∫ x in distBall X.metric.form o R, |w x| ∂μ :=
    (integral_mono_ae hfi hχw (ae_of_all _ hfΔ)).trans (hswap.le.trans hu)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0)]
  have h := ENNReal.ofReal_le_ofReal hb
  rw [ENNReal.ofReal_mul hK,
    ofReal_integral_eq_lintegral_ofReal habs (ae_of_all _ fun x => abs_nonneg (w x))] at h
  exact h

end Yau.NodeProofs.P08Aux.ScalarAverage
