import Yau.Proofs.F02Green
import Yau.Proofs.F02InitialRicci
import Yau.Proofs.F02Regularity

/-! Actual volume and integral transport for the original metric defect. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.F02Aux
open Yau Blueprint
open LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem distBall_measure_lt_top (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {R : ℝ} (hR : 0 < R) :
    μ (distBall g.form o R) < ⊤ := by
  have : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  exact (measure_mono (show distBall g.form o R ⊆
    {x | inducedDistance g.form o x ≤ R} from
      fun x hx => ((LeafProofs.L12Aux.mem_distBall_iff g o x hR).mp hx).le)).trans_lt
    (LeafProofs.L12Aux.isCompact_inducedDistance_sublevel g o R).measure_lt_top

/-- Only finite ball volume is needed for this comparison; positivity or
cancellation of an extended real volume is not assumed. -/
theorem ballIntegralLE_iff_real (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) (f : M.Carrier → ℝ)
    {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hfi : IntegrableOn f (distBall g.form o R) μ) (hf0 : ∀ x, 0 ≤ f x) :
    BallIntegralLE g.form μ o f R B ↔
      (∫ x in distBall g.form o R, f x ∂μ) ≤ B * (μ (distBall g.form o R)).toReal := by
  unfold BallIntegralLE
  have hmass : ENNReal.ofReal B * μ (distBall g.form o R) =
      ENNReal.ofReal (B * (μ (distBall g.form o R)).toReal) := by
    rw [ENNReal.ofReal_mul hB,
      ENNReal.ofReal_toReal (distBall_measure_lt_top g μ hμ o hR).ne]
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0), hmass]
  exact ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB ENNReal.toReal_nonneg)

theorem initial_scalarCurvature_nonneg (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) (x : Pt X) :
    0 ≤ scalarCurvature X.metric.form x :=
  traceWith_nonneg _ _
    (hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef
    (initialRicci_posSemidef X o h U P ρ hf x)

theorem metricDefect_smooth_of_G04 (hG04 : G04) (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) :
    SmoothFn (fun x => traceWith (gMat X.metric.form x)
      (gMat X.metric.form x - gMat (h t) x)) := by
  have hUs := LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.1 ht
  have hR := scalarCurvature_smooth_of_G04 hG04 X
  have hL := smoothFn_laplacian X.metric hUs
  have heq : (fun x => traceWith (gMat X.metric.form x)
      (gMat X.metric.form x - gMat (h t) x)) =
      fun x => t * scalarCurvature X.metric.form x - laplacian X.metric.form (fun y => U y t) x :=
    funext (metricDefect_potential_identity X o h U P ρ hf ht)
  rw [heq]
  exact fun x => (contDiffOn_const.mul (hR x)).sub (hL x)

theorem integral_cutoff_le_ball (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) {R : ℝ} (hR : 0 < R)
    {f χ : M.Carrier → ℝ} (hf : SmoothFn f) (hχ : SmoothFn χ)
    (hcχ : HasCompactSupport χ) (hχs : tsupport χ ⊆ distBall g.form o R)
    (hf0 : ∀ x, 0 ≤ f x) (hχ1 : ∀ x, χ x ≤ 1) :
    (∫ x, χ x * f x ∂μ) ≤ ∫ x in distBall g.form o R, f x ∂μ := by
  have hχfi := smoothFn_integrable_compact g μ hμ (smoothFn_mul hχ hf) hcχ.mul_right
  have heq : (∫ x in distBall g.form o R, χ x * f x ∂μ) = ∫ x, χ x * f x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hχs h)), zero_mul]
  rw [← heq]
  exact setIntegral_mono_on hχfi.integrableOn
    (smoothFn_integrableOn_distBall g μ hμ hf o hR)
    (LeafProofs.L12Aux.isOpen_distBall g o R).measurableSet
    (fun x _ => mul_le_of_le_one_left (hf0 x) (hχ1 x))

/-- The paper's actual cutoff inequality, with the potential term on the
larger ball and the same measure throughout. -/
theorem metricDefect_integral_cutoff_bound (hG04 : G04)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ)
    {t L R K : ℝ} (ht : 0 ≤ t) (_hL : 0 < L) (hR : 0 < R) (_hK : 0 ≤ K)
    (χ : Pt X → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ)
    (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hχone : ∀ x ∈ distBall X.metric.form o L, χ x = 1)
    (hχs : tsupport χ ⊆ distBall X.metric.form o R)
    (hχlap : ∀ x, |laplacian X.metric.form χ x| ≤ K) :
    (∫ x in distBall X.metric.form o L,
      traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x) ∂μ) ≤
      t * (∫ x in distBall X.metric.form o R, scalarCurvature X.metric.form x ∂μ) +
        K * (∫ x in distBall X.metric.form o R, -U x t ∂μ) := by
  let a := fun x => traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x)
  let v := fun x => -U x t
  have ha := metricDefect_smooth_of_G04 hG04 X o h U P ρ hf ht
  have ha0 : ∀ x, 0 ≤ a x := fun x => (metricDefect_trace_bounds X o h U P ρ hf ht x).1
  have hUs := LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.1 ht
  have hv : SmoothFn v := fun x => (hUs x).neg
  have hv0 : ∀ x, 0 ≤ v x := fun x => neg_nonneg.mpr (potential_nonpos X o h U P ρ hf ht x)
  have hRs := scalarCurvature_smooth_of_G04 hG04 X
  have hR0 := initial_scalarCurvature_nonneg X o h U P ρ hf
  have hχa := smoothFn_integrable_compact X.metric μ hμ (smoothFn_mul hχ ha) hcχ.mul_right
  have hχR := smoothFn_integrable_compact X.metric μ hμ (smoothFn_mul hχ hRs) hcχ.mul_right
  obtain ⟨hχU, hUχ, hswap⟩ := integral_laplacian_swap_compact X.metric X.kahler_metric μ hμ
    hUs hχ hcχ o hR hχs
  have hvχ : Integrable (fun x => v x * laplacian X.metric.form χ x) μ := by
    convert hUχ.neg using 1
    funext x
    dsimp [v]
    ring
  have haBound : (∫ x in distBall X.metric.form o L, a x ∂μ) ≤ ∫ x, χ x * a x ∂μ := by
    have heq : (∫ x in distBall X.metric.form o L, a x ∂μ) =
        ∫ x in distBall X.metric.form o L, χ x * a x ∂μ := by
      apply setIntegral_congr_fun (LeafProofs.L12Aux.isOpen_distBall X.metric o L).measurableSet
      intro x hx
      change a x = χ x * a x
      rw [hχone x hx, one_mul]
    rw [heq]
    exact setIntegral_le_integral hχa (ae_of_all _ (fun x => mul_nonneg (hχ01 x).1 (ha0 x)))
  have hRBound := integral_cutoff_le_ball X.metric μ hμ o hR hRs hχ hcχ hχs hR0
    (fun x => (hχ01 x).2)
  have hvBound : (∫ x, v x * laplacian X.metric.form χ x ∂μ) ≤
      K * (∫ x in distBall X.metric.form o R, v x ∂μ) := by
    have heq : (∫ x in distBall X.metric.form o R, v x * laplacian X.metric.form χ x ∂μ) =
        ∫ x, v x * laplacian X.metric.form χ x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [laplacian_zero_off_tsupport _ χ (fun h => hx (hχs h)), mul_zero]
    rw [← heq, ← integral_const_mul]
    exact setIntegral_mono_on hvχ.integrableOn
      ((smoothFn_integrableOn_distBall X.metric μ hμ hv o hR).const_mul K)
      (LeafProofs.L12Aux.isOpen_distBall X.metric o R).measurableSet
      (fun x _ => by
        have hle := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hχlap x)) (hv0 x)
        simpa only [mul_comm] using hle)
  have hidentity : (∫ x, χ x * a x ∂μ) =
      t * (∫ x, χ x * scalarCurvature X.metric.form x ∂μ) +
        ∫ x, v x * laplacian X.metric.form χ x ∂μ := by
    have heq : (fun x => χ x * a x) =
        fun x => t * (χ x * scalarCurvature X.metric.form x) -
          χ x * laplacian X.metric.form (fun y => U y t) x := by
      funext x
      dsimp [a]
      rw [metricDefect_potential_identity X o h U P ρ hf ht]
      ring
    rw [heq, integral_sub (hχR.const_mul t) hχU, integral_const_mul, hswap]
    have hneg : (∫ x, v x * laplacian X.metric.form χ x ∂μ) =
        -(∫ x, U x t * laplacian X.metric.form χ x ∂μ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by dsimp [v]; ring)
    linarith
  exact haBound.trans (hidentity.le.trans (add_le_add (mul_le_mul_of_nonneg_left hRBound ht) hvBound))

end Yau.Proofs.F02Aux
