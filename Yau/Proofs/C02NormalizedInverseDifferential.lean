import Yau.Proofs.C02NormalizedInverseSource
import Yau.Proofs.C02IntertwiningComposition

/-! The normalized inverse has the actual inverse differential at each
point. The physical normalization cancels the auxiliary dilation exactly. -/

noncomputable section
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedInverseSource_hasFDerivAt
    (e : OpenPartialHomeomorph E E) (r : ℝ) (hr : r ≠ 0) (z : E)
    (hy : e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z ∈ e.target)
    (hf : DifferentiableAt ℝ (e : E → E)
      (e.symm (e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z)))
    (hInv : (fderiv ℝ (e : E → E)
      (e.symm (e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z))).IsInvertible) :
    HasFDerivAt (normalizedInverseSource e r)
      (Real.sqrt (2 : ℝ) •
        (fderiv ℝ (e : E → E)
          (e.symm (e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z))).inverse.comp
            (fderiv ℝ (e : E → E) 0)) z := by
  let y := e 0 + (Real.sqrt (2 : ℝ) / r) • fderiv ℝ (e : E → E) 0 z
  let D := fderiv ℝ (e : E → E) (e.symm y)
  let D0 := fderiv ℝ (e : E → E) 0
  let S := (Real.sqrt (2 : ℝ) / r) • D0
  obtain ⟨L, hL⟩ := hInv
  have hd : HasFDerivAt (e : E → E) (L : E →L[ℝ] E) (e.symm y) := by
    rw [hL]
    exact hf.hasFDerivAt
  have hBack : HasFDerivAt e.symm D.inverse y := by
    have hLD : (L : E →L[ℝ] E) = D := hL
    rw [← hLD, ContinuousLinearMap.inverse_equiv]
    exact e.hasFDerivAt_symm hy hd
  have hT : HasFDerivAt (fun w => e 0 + S w) S z := S.hasFDerivAt.const_add (e 0)
  have hG := (hBack.comp z hT).const_smul r
  have hDerivative : r • D.inverse.comp S =
      Real.sqrt (2 : ℝ) • D.inverse.comp D0 := by
    apply ContinuousLinearMap.ext
    intro v
    change r • D.inverse ((Real.sqrt (2 : ℝ) / r) • D0 v) =
      Real.sqrt (2 : ℝ) • D.inverse (D0 v)
    rw [map_smul, smul_smul]
    congr 1
    field_simp
  rw [hDerivative] at hG
  exact hG

theorem normalized_inverse_differential_intertwines
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D D0 J : E →L[ℝ] E) (hD : D.IsInvertible)
    (hForward : ∀ v, D (J v) = Complex.I • D v)
    (hZero : ∀ v, D0 (Complex.I • v) = Complex.I • D0 v) (v : E) :
    (Real.sqrt (2 : ℝ) • D.inverse.comp D0) (Complex.I • v) =
      J ((Real.sqrt (2 : ℝ) • D.inverse.comp D0) v) := by
  change Real.sqrt (2 : ℝ) • D.inverse (D0 (Complex.I • v)) =
    J (Real.sqrt (2 : ℝ) • D.inverse (D0 v))
  rw [hZero, inverse_differential_intertwines D J hD hForward, map_smul]

end Yau.Blueprint.C02Proof
