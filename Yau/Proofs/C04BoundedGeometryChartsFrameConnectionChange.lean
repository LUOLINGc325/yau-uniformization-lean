import Yau.Proofs.C04BoundedGeometryChartsFrameConnection

/-! Coordinate invariance of the connection of the same moving frame. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C04ChartsAux
open Yau
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem coordinateFrameConnection_change
    (Γ Δ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z W f : ComplexVector n → ComplexVector n)
    (P Q : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (v u w : ComplexVector n)
    (hZ : DifferentiableAt ℝ Z v) (hP : DifferentiableAt ℝ P v)
    (hQ : DifferentiableAt ℝ Q v) (hf : ContDiffAt ℝ 2 f (Z v))
    (hW : W =ᶠ[𝓝 v] (f ∘ Z))
    (hPQ : Q =ᶠ[𝓝 v] (fun z => (fderiv ℝ f (Z z)).comp (P z)))
    (hΓ : ∀ a b, fderiv ℝ f (Z v) (Γ (Z v) a b) =
      fderiv ℝ (fderiv ℝ f) (Z v) a b +
        Δ (f (Z v)) (fderiv ℝ f (Z v) a) (fderiv ℝ f (Z v) b))
    (hiP : (P v).IsInvertible) (hiQ : (Q v).IsInvertible) :
    coordinateFrameConnection Γ Z P v u w = coordinateFrameConnection Δ W Q v u w := by
  have hfD := hf.differentiableAt (by norm_num)
  have hfDD := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hDW : fderiv ℝ W v = (fderiv ℝ f (Z v)).comp (fderiv ℝ Z v) := by
    rw [hW.fderiv_eq, fderiv_comp v hfD hZ]
  have hQv := hPQ.self_of_nhds
  have hWv := hW.self_of_nhds
  have hDF := hfDD.hasFDerivAt.comp v hZ.hasFDerivAt
  have hPcol := hP.hasFDerivAt.clm_apply (hasFDerivAt_const w v)
  have hcomp := hDF.clm_apply hPcol
  have hcol : (fun z => Q z w) =ᶠ[𝓝 v]
      (fun z => fderiv ℝ f (Z z) (P z w)) := by
    filter_upwards [hPQ] with z hz
    rw [hz, ContinuousLinearMap.comp_apply]
  have Hcol := hcomp.congr_of_eventuallyEq hcol
  have hDQ : fderiv ℝ Q v u w =
      fderiv ℝ f (Z v) (fderiv ℝ P v u w) +
        fderiv ℝ (fderiv ℝ f) (Z v) (fderiv ℝ Z v u) (P v w) := by
    have H := congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L u) Hcol.fderiv
    rw [fderiv_clm_apply hQ (differentiableAt_const w)] at H
    simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, fderiv_const_apply, ContinuousLinearMap.zero_apply,
      map_zero, zero_add, Function.comp_def] using H
  apply hiQ.injective
  rw [coordinateFrameConnection_equation Δ W Q v u w hiQ, hDQ, hDW, hWv, hQv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [coordinateFrameConnection_equation Γ Z P v u w hiP, map_add, hΓ]
  abel

end Yau.Proofs.C04ChartsAux
