import Yau.Proofs.C04RadialIntegralJetsCompact

/-! Every actual derivative passes through the same compact parameter integral. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false

universe u
variable {E G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

theorem radialIntegral_partial_eq_fderiv (H : E × ℝ → G) (hH : ContDiff ℝ ∞ H) (t : ℝ) :
    (fun x => radialIntegralPartial H (x,t)) = fderiv ℝ (fun x => H (x,t)) := by
  funext x
  exact (radialIntegralPartial_hasFDerivAt H (hH.differentiable (by simp) (x,t))).fderiv.symm

theorem radialIntegral_partial_contDiff_infty (H : E × ℝ → G) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (radialIntegralPartial H) := by
  exact (hH.fderiv_right (by simp)).clm_comp contDiff_const

theorem radialIntegral_sliceJet_contDiff (H : E × ℝ → G) (hH : ContDiff ℝ ∞ H) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedFDeriv ℝ m (fun x => H (x,p.2)) p.1) := by
  induction m generalizing G with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, Function.comp_def] using
      (continuousMultilinearCurryFin0 ℝ E G).symm.contDiff.comp hH
  | succ m IH =>
    let L := (continuousMultilinearCurryRightEquiv' ℝ m E G).symm
    have hpart := radialIntegral_partial_contDiff_infty H hH
    have hI := IH (radialIntegralPartial H) hpart
    have heq : (fun p : E × ℝ => iteratedFDeriv ℝ (m + 1) (fun x => H (x,p.2)) p.1) =
        fun p : E × ℝ => L (iteratedFDeriv ℝ m (fun x => radialIntegralPartial H (x,p.2)) p.1) := by
      funext p
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
        ← radialIntegral_partial_eq_fderiv H hH p.2]
    rw [heq]
    simpa only [Function.comp_def] using L.contDiff.comp hI

theorem radialIntegral_iteratedFDeriv (H : E × ℝ → G) (hH : ContDiff ℝ ∞ H) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ m (fun y => ∫ t in (0 : ℝ)..1, H (y,t)) x =
      ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ m (fun y => H (y,t)) x := by
  induction m generalizing G with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.coe_toLinearIsometry] using
      (LinearIsometry.intervalIntegral_comp_comm (𝕜 := ℝ) (E := G) (F := E [×0]→L[ℝ] G)
        (continuousMultilinearCurryFin0 ℝ E G).symm.toLinearIsometry (fun t : ℝ => H (x,t))).symm
  | succ m IH =>
    let L := (continuousMultilinearCurryRightEquiv' ℝ m E G).symm
    have hpart := radialIntegral_partial_contDiff_infty H hH
    have hderiv : fderiv ℝ (fun y => ∫ t in (0 : ℝ)..1, H (y,t)) =
        fun y => ∫ t in (0 : ℝ)..1, radialIntegralPartial H (y,t) := by
      funext y
      exact (radialIntegral_joint_hasFDerivAt H (hH.of_le (by simp)) y).fderiv
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, hderiv,
      IH (radialIntegralPartial H) hpart]
    change L (∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ m (fun y => radialIntegralPartial H (y,t)) x) = _
    have hL := LinearIsometry.intervalIntegral_comp_comm (𝕜 := ℝ)
      (E := E [×m]→L[ℝ] E →L[ℝ] G) (F := E [×(m + 1)]→L[ℝ] G)
      (a := (0 : ℝ)) (b := 1) (μ := volume)
      L.toLinearIsometry (fun t : ℝ => iteratedFDeriv ℝ m (fun y => radialIntegralPartial H (y,t)) x)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hL
    rw [← hL]
    congr 1
    funext t
    rw [radialIntegral_partial_eq_fderiv H hH t]
    exact (iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := fun y => H (y,t)) (n := m) (x := x)).symm

end Yau.Proofs.C04Aux
