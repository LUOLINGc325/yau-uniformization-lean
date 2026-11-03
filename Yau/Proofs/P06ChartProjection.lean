import Yau.Proofs.P06ChartProjectionBounds

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem chartFunctional_add (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) (A B : RealForm M k) :
    chartFunctional x φ L (A + B) = chartFunctional x φ L A + chartFunctional x φ L B := by
  funext z
  have he : chartForm (A + B) x z = chartForm A x z + chartForm B x z := by
    ext v
    simp [chartForm]
  simp only [chartFunctional, he, map_add, Pi.add_apply, mul_add]

theorem chartFunctional_smul (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) (a : ℝ) (A : RealForm M k) :
    chartFunctional x φ L (a • A) = a • chartFunctional x φ L A := by
  funext z
  have he : chartForm (a • A) x z = a • chartForm A x z := by
    ext v
    simp [chartForm]
  simp only [chartFunctional, he, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

def chartProjectionLinear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    L2FormSpace g μ k →ₗ[ℝ] Lp ℝ 2 (lebesgueC n) where
  toFun u := (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L u.toSection u.toSection_l2).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L
      (u + v).toSection (u + v).toSection_l2),
      Lp.coeFn_add
        ((chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L u.toSection u.toSection_l2).toLp _)
        ((chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L v.toSection v.toSection_l2).toLp _),
      MemLp.coeFn_toLp (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L u.toSection u.toSection_l2),
      MemLp.coeFn_toLp (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L v.toSection v.toSection_l2)]
      with z hz hadd hu hv
    rw [hz, hadd, Pi.add_apply, hu, hv]
    exact congrFun (chartFunctional_add x φ L u.toSection v.toSection) z
  map_smul' a u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L
      (a • u).toSection (a • u).toSection_l2),
      Lp.coeFn_smul a
        ((chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L u.toSection u.toSection_l2).toLp _),
      MemLp.coeFn_toLp (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L u.toSection u.toSection_l2)]
      with z hz hsmul hu
    simp only [RingHom.id_apply]
    rw [hz, hsmul, Pi.smul_apply, hu]
    exact congrFun (chartFunctional_smul x φ L a u.toSection) z

theorem chartProjectionLinear_norm_sq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) (u : L2FormSpace g μ k) :
    ‖chartProjectionLinear g μ hμ x φ hφ hcφ hφO L u‖ ^ 2 =
      ∫ z, (chartFunctional x φ L u.toSection z) ^ 2 ∂lebesgueC n := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L
    u.toSection u.toSection_l2)] with z hz
  change inner ℝ ((chartProjectionLinear g μ hμ x φ hφ hcφ hφO L u) z)
    ((chartProjectionLinear g μ hμ x φ hφ hcφ hφO L u) z) = _
  rw [show (chartProjectionLinear g μ hμ x φ hφ hcφ hφO L u) z =
    chartFunctional x φ L u.toSection z from hz]
  simp only [RCLike.inner_apply, conj_trivial, sq]

theorem chartProjectionLinear_bounded (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : L2FormSpace g μ k,
      ‖chartProjectionLinear g μ hμ x φ hφ hcφ hφO L u‖ ≤ B * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := chartFunctional_integral_bound g μ hμ x φ hφ hcφ hφO L
  refine ⟨C + 1, by linarith, ?_⟩
  intro u
  have hs := hb u.toSection u.toSection_l2
  rw [← chartProjectionLinear_norm_sq g μ hμ x φ hφ hcφ hφO L] at hs
  have he : ‖realizeActualForm g μ u.toSection u.toSection_l2‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [realizeActualForm_norm_sq, l2FormSpace_norm_sq]
  rw [he] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) (norm_nonneg u))).mp
  rw [mul_pow]
  exact hs.trans (mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg ‖u‖))

def chartProjectionCore (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    L2FormSpace g μ k →L[ℝ] Lp ℝ 2 (lebesgueC n) :=
  (chartProjectionLinear g μ hμ x φ hφ hcφ hφO L).mkContinuous
    (chartProjectionLinear_bounded g μ hμ x φ hφ hcφ hφO L).choose
    (chartProjectionLinear_bounded g μ hμ x φ hφ hcφ hφO L).choose_spec.2

/-- The actual fixed-chart compact projection, extended from all raw L²
forms to the separated original Hodge Hilbert completion. -/
def chartProjection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    L2FormHilbert g μ k →L[ℝ] Lp ℝ 2 (lebesgueC n) :=
  (chartProjectionCore g μ hμ x φ hφ hcφ hφO L).fromCompletion

theorem chartProjection_actual (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ chartTarget x)
    (L : ((ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    chartProjection g μ hμ x φ hφ hcφ hφO L (realizeActualForm g μ A hA) =
      (chartFunctional_memLp g μ hμ x φ hφ hcφ hφO L A hA).toLp _ := by
  exact ContinuousLinearMap.fromCompletion_apply_coe
    (chartProjectionCore g μ hμ x φ hφ hcφ hφO L) (L2FormSpace.ofSection A hA)

end Yau.NodeProofs.P06Aux
