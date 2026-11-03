import Yau.Proofs.C04BoundedGeometryChartsFrameConnection

/-! Torsion vanishes in the induced coframe of an actual torsion-free coordinate connection. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem coordinateFrameConnection_torsion
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z : ComplexVector n → ComplexVector n)
    (P A : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (v u w : ComplexVector n) (hZ : ContDiffAt ℝ 2 Z v)
    (hP : DifferentiableAt ℝ P v) (hA : DifferentiableAt ℝ A v)
    (hiP : (P v).IsInvertible)
    (hPA : (fun z => (P z).comp (A z)) =ᶠ[𝓝 v] fderiv ℝ Z)
    (hΓ : ∀ a b, Γ (Z v) a b = Γ (Z v) b a) :
    fderiv ℝ A v u w - fderiv ℝ A v w u +
      coordinateFrameConnection Γ Z P v u (A v w) -
        coordinateFrameConnection Γ Z P v w (A v u) = 0 := by
  have hPA₀ (a : ComplexVector n) : P v (A v a) = fderiv ℝ Z v a :=
    congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L a) hPA.self_of_nhds
  have hDZ := (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hD (a b : ComplexVector n) :
      fderiv ℝ (fderiv ℝ Z) v a b = P v (fderiv ℝ A v a b) + fderiv ℝ P v a (A v b) := by
    have H := hP.hasFDerivAt.clm_apply (hA.hasFDerivAt.clm_apply (hasFDerivAt_const b v))
    have H' := hDZ.hasFDerivAt.clm_apply (hasFDerivAt_const b v)
    have heq : (fun z => P z (A z b)) =ᶠ[𝓝 v] (fun z => fderiv ℝ Z z b) := by
      filter_upwards [hPA] with z hz
      exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L b) hz
    have H'' := H.congr_of_eventuallyEq heq.symm
    have he := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L a) (H'.unique H'')
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply, ContinuousLinearMap.flip_apply,
      map_zero, zero_add] using he
  apply hiP.injective
  simp only [map_sub, map_add, map_zero,
    coordinateFrameConnection_equation Γ Z P v u (A v w) hiP,
    coordinateFrameConnection_equation Γ Z P v w (A v u) hiP, hPA₀]
  have hsym := hZ.isSymmSndFDerivAt (by norm_num) u w
  rw [hΓ (fderiv ℝ Z v u) (fderiv ℝ Z v w)]
  have H₁ := hD u w
  have H₂ := hD w u
  rw [← hsym] at H₂
  calc
    _ = (P v (fderiv ℝ A v u w) + fderiv ℝ P v u (A v w)) -
        (P v (fderiv ℝ A v w u) + fderiv ℝ P v w (A v u)) := by abel
    _ = 0 := sub_eq_zero.mpr (H₁.symm.trans H₂)

end Yau.Proofs.C04ChartsAux
