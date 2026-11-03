import Yau.LeafProofs.L19HeatMarkovMultiplier
import Yau.LeafProofs.L19ScalarResolventRelation
import Yau.LeafProofs.L19HeatFamilyDerivative

/-! The actual variational Euler resolvents are rational functions of the
fixed complex resolvent. No spectral identity is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section Complexification
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem heatLp_ext {f k : Lp ℂ 2 μ} (hr : heatLpRe μ f = heatLpRe μ k)
    (hi : heatLpIm μ f = heatLpIm μ k) : f = k := by
  rw [← heatLp_decomposition μ f, ← heatLp_decomposition μ k, hr, hi]

@[simp] theorem heatComplexify_add (S T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    heatComplexify μ (S + T) = heatComplexify μ S + heatComplexify μ T := by
  apply ContinuousLinearMap.ext
  intro f
  apply heatLp_ext μ <;> simp only [add_apply, map_add, heatComplexify_re, heatComplexify_im]

@[simp] theorem heatComplexify_smul (r : ℝ) (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    heatComplexify μ (r • T) = r • heatComplexify μ T := by
  apply ContinuousLinearMap.ext
  intro f
  apply heatLp_ext μ <;> simp only [smul_apply, map_smul, heatComplexify_re, heatComplexify_im]

@[simp] theorem heatComplexify_mul (S T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    heatComplexify μ (S * T) = heatComplexify μ S * heatComplexify μ T := by
  apply ContinuousLinearMap.ext
  intro f
  apply heatLp_ext μ <;> simp only [mul_apply_eq_comp, heatComplexify_re, heatComplexify_im]

@[simp] theorem heatComplexify_one :
    heatComplexify μ (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply heatLp_ext μ <;> simp only [one_apply_eq_self, heatComplexify_re, heatComplexify_im]

@[simp] theorem heatComplexify_pow (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (j : ℕ) :
    heatComplexify μ (T ^ j) = heatComplexify μ T ^ j := by
  induction j with
  | zero => simp
  | succ j hj => simp [pow_succ, hj]

@[simp] theorem heatRealRestrictionCLM_complexify (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    heatRealRestrictionCLM μ (heatComplexify μ T) = T := by
  apply ContinuousLinearMap.ext
  intro f
  exact (heatComplexify_re μ T (heatLpOfReal μ f)).trans (congrArg T (heatLpRe_ofReal μ f))

end Complexification
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual Euler operator relation, complexified by the explicit L² maps. -/
theorem scalarComplexEuler_relation (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) :
    heatComplexify μ (scalarResolvent g μ hμ h hh) *
      (h • (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) + (1 - h) • scalarComplexResolvent g μ hμ) =
        scalarComplexResolvent g μ hμ := by
  have heq := congrArg (heatComplexify μ)
    (scalarResolvent_euler_operator_relation g μ hμ h hh)
  change heatComplexify μ (scalarResolvent g μ hμ h hh *
    (h • 1 + (1 - h) • scalarResolvent g μ hμ 1 zero_lt_one)) =
      scalarComplexResolvent g μ hμ at heq
  simpa only [heatComplexify_mul, heatComplexify_add, heatComplexify_smul,
    heatComplexify_one, scalarComplexResolvent] using heq

/-- The rational CFC formula is forced by the genuine variational relation. -/
theorem scalarResolvent_complexify_eq_cfc (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (h : ℝ) (hh : 0 < h) :
    heatComplexify μ (scalarResolvent g μ hμ h hh) =
      cfc (scalarEulerMultiplier h) (scalarComplexResolvent g μ hμ) := by
  let B := scalarComplexResolvent g μ hμ
  have hB : IsSelfAdjoint B := scalarComplexResolvent_selfAdjoint g μ hμ
  let d : ℝ → ℝ := fun s => h + (1 - h) * s
  have hd : ContinuousOn d (spectrum ℝ B) := by fun_prop
  have hdn : ∀ s ∈ spectrum ℝ B, d s ≠ 0 := fun s hs =>
    (scalarEuler_denominator_pos hh (scalarComplexResolvent_spectrum g μ hμ hs)).ne'
  have hdi := hd.inv₀ hdn
  have hT : cfc d B = h • (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) + (1 - h) • B := by
    change cfc (fun s => h + (1 - h) * s) B = _
    rw [cfc_add (a := B) (fun _ => h) (fun s => (1 - h) * s) continuous_const.continuousOn (by fun_prop), cfc_const h B hB,
      Algebra.algebraMap_eq_smul_one, cfc_const_mul_id (1 - h) B hB]
  have hTD : cfc d B * cfc (fun s => (d s)⁻¹) B = 1 := by
    rw [← cfc_mul d (fun s => (d s)⁻¹) B hd hdi, ← cfc_const_one ℝ B hB]
    exact cfc_congr fun s hs => mul_inv_cancel₀ (hdn s hs)
  have hR := scalarComplexEuler_relation g μ hμ h hh
  change heatComplexify μ (scalarResolvent g μ hμ h hh) *
    (h • 1 + (1 - h) • B) = B at hR
  rw [← hT] at hR
  calc
    heatComplexify μ (scalarResolvent g μ hμ h hh) =
        heatComplexify μ (scalarResolvent g μ hμ h hh) *
          (cfc d B * cfc (fun s => (d s)⁻¹) B) := by rw [hTD, mul_one]
    _ = B * cfc (fun s => (d s)⁻¹) B := by rw [← mul_assoc, hR]
    _ = cfc (scalarEulerMultiplier h) B := by
      calc
        _ = cfc (fun s : ℝ => s) B * cfc (fun s => (d s)⁻¹) B := by rw [cfc_id' ℝ B hB]
        _ = cfc (fun s => s * (d s)⁻¹) B := (cfc_mul _ _ B continuous_id.continuousOn hdi).symm
        _ = _ := rfl

end Yau.LeafProofs.L19Aux
