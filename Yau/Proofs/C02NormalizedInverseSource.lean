import Yau.Proofs.C02QuantitativeInverseSmooth

/-! The normalization uses physical sqrt(2) only in the source map. Its
actual derivative at zero is exactly sqrt(2) times the identity. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalizedInverseSource (e : OpenPartialHomeomorph E E) (r : ℝ) (z : E) : E :=
  r • e.symm (e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z)

theorem normalizedInverseSource_zero (e : OpenPartialHomeomorph E E)
    (he0 : (0 : E) ∈ e.source) (r : ℝ) : normalizedInverseSource e r 0 = 0 := by
  simp only [normalizedInverseSource, map_zero, smul_zero, add_zero, e.left_inv he0]

theorem normalizedInverseSource_hasFDerivAt_zero
    (e : OpenPartialHomeomorph E E) (he0 : (0 : E) ∈ e.source)
    (hf : DifferentiableAt ℝ (e : E → E) 0)
    (hInv : (fderiv ℝ (e : E → E) 0).IsInvertible) (r : ℝ) (hr : r ≠ 0) :
    HasFDerivAt (normalizedInverseSource e r)
      (Real.sqrt (2 : ℝ) • ContinuousLinearMap.id ℝ E) 0 := by
  let D := fderiv ℝ (e : E → E) 0
  let S := (Real.sqrt (2 : ℝ) / r) • D
  obtain ⟨L, hL⟩ := hInv
  have hDInv : D.IsInvertible := ⟨L, hL⟩
  have hd : HasFDerivAt (e : E → E) (L : E →L[ℝ] E) 0 := by rw [hL]; exact hf.hasFDerivAt
  have hBack : HasFDerivAt e.symm D.inverse (e 0) := by
    have hd' : HasFDerivAt (e : E → E) (L : E →L[ℝ] E) (e.symm (e 0)) := by
      rw [e.left_inv he0]
      exact hd
    have hh := e.hasFDerivAt_symm (e.map_source he0) hd'
    simpa only [D, ← hL, ContinuousLinearMap.inverse_equiv] using hh
  have hT : HasFDerivAt (fun z => e 0 + S z) S 0 := S.hasFDerivAt.const_add (e 0)
  have hBack' : HasFDerivAt e.symm D.inverse ((fun z => e 0 + S z) 0) := by
    simpa only [map_zero, add_zero] using hBack
  have hG := (hBack'.comp 0 hT).const_smul r
  have hDerivative : r • D.inverse.comp S = Real.sqrt (2 : ℝ) • ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    change r • D.inverse ((Real.sqrt (2 : ℝ) / r) • D v) = Real.sqrt (2 : ℝ) • v
    rw [map_smul, hDInv.inverse_apply_self, smul_smul]
    congr 1
    field_simp
  rw [hDerivative] at hG
  exact hG

end Yau.Blueprint.C02Proof
