import Yau.Proofs.P06ChartProjection

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem chartFunctional_sub (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) (A B : RealForm M k) :
    chartFunctional x φ L (A - B) = chartFunctional x φ L A - chartFunctional x φ L B := by
  funext z
  have he : chartForm (A - B) x z = chartForm A x z - chartForm B x z := by
    ext v
    simp [chartForm]
  simp only [chartFunctional, he, map_sub, Pi.sub_apply, mul_sub]

theorem chartProjection_actual_ae (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    (chartProjection g μ hμ x φ hφ hcφ hφO L (realizeActualForm g μ A hA) :
      ComplexVector n → ℝ) =ᵐ[lebesgueC n] chartFunctional x φ L A := by
  rw [chartProjection_actual]
  exact MemLp.coeFn_toLp _

theorem chartProjection_tendsto {ι : Type*} {l : Filter ι}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    {u : ι → L2FormHilbert g μ k} {v : L2FormHilbert g μ k} (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun i => chartProjection g μ hμ x φ hφ hcφ hφO L (u i)) l
      (𝓝 (chartProjection g μ hμ x φ hφ hcφ hφO L v)) :=
  (chartProjection g μ hμ x φ hφ hcφ hφO L).continuous.tendsto v |>.comp hu

/-- Strong convergence in the original integrated metric gives strong L²
convergence of every actual compact-cutoff chart component, for every
filter. No coordinate convergence hypothesis is added to a graph domain. -/
theorem chartFunctional_strong_l2_tendsto {ι : Type*} {l : Filter ι}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (As : ι → RealForm M k) (A : RealForm M k)
    (hAs : ∀ i, L2RealForm g.form μ (As i)) (hA : L2RealForm g.form μ A)
    (ht : Tendsto (fun i => realizeActualForm g μ (As i) (hAs i)) l
      (𝓝 (realizeActualForm g μ A hA))) :
    Tendsto (fun i => ∫ z, (φ z *
      (L (chartForm (As i) x z) - L (chartForm A x z))) ^ 2 ∂lebesgueC n) l (𝓝 0) := by
  let P := chartProjection g μ hμ x φ hφ hcφ hφO L
  have hp := chartProjection_tendsto g μ hμ x φ hφ hcφ hφO L ht
  have hc : Tendsto (fun _ : ι => P (realizeActualForm g μ A hA)) l
      (𝓝 (P (realizeActualForm g μ A hA))) := tendsto_const_nhds
  have hn : Tendsto (fun i => ‖P (realizeActualForm g μ (As i) (hAs i)) -
      P (realizeActualForm g μ A hA)‖ ^ 2) l (𝓝 0) := by
    simpa only [P, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      (hp.sub hc).norm.pow 2
  apply hn.congr'
  filter_upwards [] with i
  have he : P (realizeActualForm g μ (As i) (hAs i)) - P (realizeActualForm g μ A hA) =
      chartProjectionLinear g μ hμ x φ hφ hcφ hφO L
        (L2FormSpace.ofSection (As i - A) (l2RealForm_sub g μ (As i) A (hAs i) hA)) := by
    rw [← map_sub, ← realizeActualForm_sub]
    exact ContinuousLinearMap.fromCompletion_apply_coe
      (chartProjectionCore g μ hμ x φ hφ hcφ hφO L)
        (L2FormSpace.ofSection (As i - A) (l2RealForm_sub g μ (As i) A (hAs i) hA))
  rw [he, chartProjectionLinear_norm_sq]
  apply integral_congr_ae
  filter_upwards [] with z
  change (chartFunctional x φ L (As i - A) z) ^ 2 = _
  rw [chartFunctional_sub]
  simp only [Pi.sub_apply, chartFunctional, mul_sub]

end Yau.NodeProofs.P06Aux
