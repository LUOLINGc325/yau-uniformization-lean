import Yau.Proofs.P06TimeIntegralPotentialIntegral

/-! Smoothness and every spatial derivative of the genuine time primitive. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.NodeProofs.P06Aux.TimePotential
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {S : Set E} (hS : IsOpen S) {u : ℝ → E → F} {f : E → F}
    (hu : ContDiffOn ℝ ∞ (fun p : E × ℝ => u p.2 p.1) (S ×ˢ Ioi 0))
    (hf : ContDiffOn ℝ ∞ f S) (hinit : CompactJetInitial (S := S) u f)
include hS hu hf hinit

/-- Currying commutes with the time integral of the next spatial jet. -/
theorem hasFDerivAt_integratedJet (j : ℕ) {z : E} (hz : z ∈ S)
    {T : ℝ} (hT : 0 < T) :
    HasFDerivAt (fun w => ∫ s in (0 : ℝ)..T, iteratedFDeriv ℝ j (u s) w)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F)
        (∫ s in (0 : ℝ)..T, iteratedFDeriv ℝ (j + 1) (u s) z)) z := by
  letI : NormedAddCommGroup (E →L[ℝ] (E [×j]→L[ℝ] F)) := inferInstance
  have hd := hasFDerivAt_integral_spatialJet hS hu hf hinit j hz hT
  let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F :
    (E [×(j + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×j]→L[ℝ] F)))
  have hc := L.intervalIntegral_comp_comm (𝕜 := ℝ)
    (E := E [×(j + 1)]→L[ℝ] F) (F := E →L[ℝ] (E [×j]→L[ℝ] F))
    (spatialJet_intervalIntegrable hS hu hf hinit (j + 1) hz hT)
  have he : (∫ s in (0 : ℝ)..T, fderiv ℝ (iteratedFDeriv ℝ j (u s)) z) =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F)
        (∫ s in (0 : ℝ)..T, iteratedFDeriv ℝ (j + 1) (u s) z) := by
    simpa only [fderiv_iteratedFDeriv, Function.comp_def, L, LinearIsometryEquiv.coe_coe''] using hc
  rw [← he]
  exact hd

/-- Each integral of a space jet is smooth; the induction uses the next
initial jet at every order. -/
theorem integratedJet_contDiffOn (j k : ℕ) {T : ℝ} (hT : 0 < T) :
    ContDiffOn ℝ k (fun z => ∫ s in (0 : ℝ)..T, iteratedFDeriv ℝ j (u s) z) S := by
  induction k generalizing j with
  | zero =>
    apply contDiffOn_zero.mpr
    intro z hz
    exact (hasFDerivAt_integratedJet hS hu hf hinit j hz hT).continuousAt.continuousWithinAt
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨fun z hz => (hasFDerivAt_integratedJet hS hu hf hinit j hz hT).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F :
    (E [×(j + 1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×j]→L[ℝ] F)))
    apply ((ih (j + 1)).continuousLinearMap_comp L).congr
    intro z hz
    exact (hasFDerivAt_integratedJet hS hu hf hinit j hz hT).fderiv

/-- The time primitive is spatially smooth on the original chart domain. -/
theorem integral_contDiffOn {T : ℝ} (hT : 0 < T) :
    ContDiffOn ℝ ∞ (fun z => ∫ s in (0 : ℝ)..T, u s z) S := by
  apply contDiffOn_infty.mpr
  intro k
  let L := (continuousMultilinearCurryFin0 ℝ E F : (E [×0]→L[ℝ] F) →L[ℝ] F)
  apply ((integratedJet_contDiffOn hS hu hf hinit 0 k hT).continuousLinearMap_comp L).congr
  intro z hz
  have hc := (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.intervalIntegral_comp_comm
    (fun s => iteratedFDeriv ℝ 0 (u s) z) (a := 0) (b := T) (μ := volume)
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply, L, LinearIsometryEquiv.coe_coe''] using hc

/-- Every spatial jet of the primitive is the corresponding integral. -/
theorem iteratedFDeriv_integral (j : ℕ) {z : E} (hz : z ∈ S)
    {T : ℝ} (hT : 0 < T) :
    iteratedFDeriv ℝ j (fun w => ∫ s in (0 : ℝ)..T, u s w) z =
      ∫ s in (0 : ℝ)..T, iteratedFDeriv ℝ j (u s) z := by
  induction j generalizing z with
  | zero =>
    have hc := (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.intervalIntegral_comp_comm
      (fun s => u s z) (a := 0) (b := T) (μ := volume)
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, LinearIsometryEquiv.coe_toLinearIsometry] using hc.symm
  | succ j ih =>
    have he : iteratedFDeriv ℝ j (fun w => ∫ s in (0 : ℝ)..T, u s w) =ᶠ[𝓝 z]
        (fun w => ∫ s in (0 : ℝ)..T, iteratedFDeriv ℝ j (u s) w) := by
      filter_upwards [hS.mem_nhds hz] with w hw
      exact ih hw
    have hd := (hasFDerivAt_integratedJet hS hu hf hinit j hz hT).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, he.fderiv_eq, hd]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm_apply_apply _

end Yau.NodeProofs.P06Aux.TimePotential
