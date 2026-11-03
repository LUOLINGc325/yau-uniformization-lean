import Yau.Proofs.C04BisectionalScalar
import Yau.Proofs.C04RescaledTubeCurvatureScaling

/-! The accepted bisectional polarization estimate on the actual rescaled
field; no curvature pinching is added to the flow assumptions. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs C04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem HermLE_scalar_upper {P H : Herm n} (hH : H.PosSemidef) {u v : ℝ}
    (hP : HermLE P ((u : ℂ) • H)) (huv : u ≤ v) : HermLE P ((v : ℂ) • H) := by
  have hp := hH.smul (Complex.nonneg_iff.2 ⟨sub_nonneg.2 huv,
    by simp only [Complex.ofReal_im]⟩ : 0 ≤ ((v - u : ℝ) : ℂ))
  have hsum := hP.add hp
  change (((v : ℂ) • H) - P).PosSemidef
  convert hsum using 1
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_sub]
  ring

theorem scaled_pointwise_bounds : ∀ n : ℕ, ∃ Cn : ℝ, 0 < Cn ∧
    ∀ (M : ComplexManifold n) (k : HermitianField M),
      MetricSmooth k → KahlerClosed k → NonnegBisectional k →
      ∀ c (hc : 0 < c) (x : M.Carrier),
        (ricci (scaleField c hc k) x).PosSemidef ∧
        HermLE (ricci (scaleField c hc k) x)
          (((scalarCurvature (scaleField c hc k) x : ℝ) : ℂ) •
            gMat (scaleField c hc k) x) ∧
        curvatureJetNorm (scaleField c hc k) 0 x ≤
          Cn * scalarCurvature (scaleField c hc k) x := by
  intro n
  obtain ⟨Cn, hCn, hpoint⟩ := C04BisectionalScalarAux.pointwise_bounds n
  refine ⟨Cn, hCn, ?_⟩
  intro M k hs hk hBC c hc x
  obtain ⟨hRic, hscalar, hupper, hRm⟩ := hpoint M k hs hk hBC x
  refine ⟨by simpa only [ricci_scaleField] using hRic, ?_, ?_⟩
  · rw [ricci_scaleField, scalar_scaleField, gMat_scaleField, smul_smul,
      ← Complex.ofReal_mul]
    have he : (c⁻¹ * scalarCurvature k x) * c = scalarCurvature k x := by field_simp
    rw [he]
    exact hupper
  · rw [curvatureJetNorm_zero_scale c hc k hs, scalar_scaleField]
    have hm := mul_le_mul_of_nonneg_left hRm (inv_nonneg.2 hc.le)
    convert hm using 1 <;> ring

theorem rescaled_gMat_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (ti R : ℝ) (hR : 0 < R) (x : Pt X) (z : ℝ)
    (htime : 0 < ti + z / R) (a b : Fin n) :
    HasDerivAt (fun w => gMat (scaleField R hR (h (ti + w / R))) x a b)
      (-(ricci (scaleField R hR (h (ti + z / R))) x) a b) z := by
  have hd := (hf.1.2.2.2 x (ti + z / R) htime.le a b).hasDerivAt
    (Ici_mem_nhds htime)
  have hp := ((hasDerivAt_id z).div_const R).const_add ti
  have hcomp := (hd.scomp z hp).const_mul (R : ℂ)
  simp only [gMat_scaleField, Matrix.smul_apply, smul_eq_mul, ricci_scaleField]
  have hRC : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR.ne'
  have hcancel (u : ℂ) : (R : ℂ) * ((1 / R : ℝ) • -u) = -u := by
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
    field_simp [hRC]
  simpa only [Function.comp_def, id_eq, hcancel] using hcomp

end Yau.Proofs.C04RescaledTubeAux
