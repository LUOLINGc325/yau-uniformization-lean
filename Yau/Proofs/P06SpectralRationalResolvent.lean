import Yau.Proofs.P06NormalizedResolvent
import Yau.Proofs.P06SpectralEulerAlgebra
import Yau.LeafProofs.L19HeatMarkovMultiplier

noncomputable section
open scoped Topology InnerProductSpace ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux
open ComplexHilbert Yau.LeafProofs.L19Aux
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (T : H →ₗ.[ℝ] H) (hd : Dense (T.domain : Set H)) (hself : T.adjoint = T)
  (hp : ∀ u : T.domain, 0 ≤ inner ℝ (u : H) (T u))
  (R : H →L[ℝ] H) (hRs : R.IsSymmetric) (hRp : ∀ x, 0 ≤ inner ℝ (R x) x)
  (hRb : ∀ x, ‖R x‖ ≤ ‖x‖) (hRi : Function.Injective R)
  (hR : R = positiveResolvent T hd hself hp 1 zero_lt_one)

include hR in
theorem normalizedResolvent_complexEuler_relation (h : ℝ) (hh : 0 < h) :
    complexify (normalizedResolvent T hd hself hp h hh) *
      (h • (1 : ComplexHilbert H →L[ℂ] ComplexHilbert H) + (1 - h) • complexify R) =
        complexify R := by
  have heq := congrArg (complexify (H := H))
    (normalizedResolvent_euler_operator_relation T hd hself hp h hh)
  rw [← hR] at heq
  simpa only [complexify_mul, complexify_add, complexify_smul, complexify_one] using heq

include hRs hRp hRb hRi hR in
/-- The rational functional calculus is derived from the actual original
unbounded resolvent graph, before any cone invariant is used. -/
theorem normalizedResolvent_complexify_eq_cfc (h : ℝ) (hh : 0 < h) :
    complexify (normalizedResolvent T hd hself hp h hh) =
      cfc (scalarEulerMultiplier h) (complexify R) := by
  let B := complexify R
  have hB : IsSelfAdjoint B := complexify_selfAdjoint R hRs
  have hσ : spectrum ℝ B ⊆ Set.Icc 0 1 :=
    Spectral.complexResolvent_spectrum R hRs hRp hRb hRi
  let d : ℝ → ℝ := fun s => h + (1 - h) * s
  have hdcont : ContinuousOn d (spectrum ℝ B) := by fun_prop
  have hdn : ∀ s ∈ spectrum ℝ B, d s ≠ 0 := fun s hs =>
    (scalarEuler_denominator_pos hh (hσ hs)).ne'
  have hdi := hdcont.inv₀ hdn
  have hD : cfc d B = h • (1 : ComplexHilbert H →L[ℂ] ComplexHilbert H) + (1 - h) • B := by
    change cfc (fun s => h + (1 - h) * s) B = _
    rw [cfc_add (a := B) (fun _ => h) (fun s => (1 - h) * s)
      continuous_const.continuousOn (by fun_prop), cfc_const h B hB,
      Algebra.algebraMap_eq_smul_one, cfc_const_mul_id (1 - h) B hB]
  have hDinv : cfc d B * cfc (fun s => (d s)⁻¹) B = 1 := by
    rw [← cfc_mul d (fun s => (d s)⁻¹) B hdcont hdi, ← cfc_const_one ℝ B hB]
    exact cfc_congr fun s hs => mul_inv_cancel₀ (hdn s hs)
  have hJ := normalizedResolvent_complexEuler_relation T hd hself hp R hR h hh
  change complexify (normalizedResolvent T hd hself hp h hh) *
    (h • 1 + (1 - h) • B) = B at hJ
  rw [← hD] at hJ
  calc
    _ = complexify (normalizedResolvent T hd hself hp h hh) *
        (cfc d B * cfc (fun s => (d s)⁻¹) B) := by rw [hDinv, mul_one]
    _ = B * cfc (fun s => (d s)⁻¹) B := by rw [← mul_assoc, hJ]
    _ = cfc (scalarEulerMultiplier h) B := by
      calc
        _ = cfc (fun s : ℝ => s) B * cfc (fun s => (d s)⁻¹) B := by rw [cfc_id' ℝ B hB]
        _ = cfc (fun s => s * (d s)⁻¹) B :=
          (cfc_mul _ _ B continuous_id.continuousOn hdi).symm
        _ = _ := rfl

end Yau.NodeProofs.P06Aux
