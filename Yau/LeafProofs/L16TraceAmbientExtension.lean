import Yau.LeafProofs.L16TraceHighHolder
import Yau.LeafProofs.L16HalfSpaceSchauderTransport

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceAmbientExtension_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceAmbientExtension_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance traceAmbientExtension_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance traceAmbientExtension_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The actual causal trace layer has ambient C² regularity after the literal
    second-order normal reflection. All jets agree with the genuine one-sided
    fields, including the lateral face and both time endpoints. -/
theorem boundaryTraceLayer_extension_jets {n : ℕ} {α F T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    {e : Space n} (he : ‖e‖ = 1) {B : Point n → ℝ}
    (hB : HolderBound α univ B F) (hPast : ∀ y s, s ≤ 0 → B (y,s) = 0) :
    let U := halfSpaceSecondOrderExtension e (boundaryTraceLayer e B)
    C2 (cylinder univ 0 T) U ∧
      EqOn U (boundaryTraceLayer e B) (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialD U) (boundaryTraceGradient e B) (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (spatialDD U) (boundaryTraceHessian e B) (cylinder {x | 0 ≤ inner ℝ e x} 0 T) ∧
      EqOn (timeD (cylinder univ 0 T) U) (boundaryTraceTimeJet e B)
        (cylinder {x | 0 ≤ inner ℝ e x} 0 T) := by
  obtain ⟨CH,hCH,hHH⟩ := boundaryTraceHessian_holder (n := n) hα hα1
  obtain ⟨Ct,hCt,hTT⟩ := boundaryTraceTimeJet_holder (n := n) hα hα1
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  have hh : ∀ s x y, |B (x,s)-B (y,s)| ≤ F*‖x-y‖^α := by
    intro s x y
    simpa only [holderWeight,sub_self,abs_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),
      add_zero,Real.norm_eq_abs] using hB.2.2 (x,s) (mem_univ _) (y,s) (mem_univ _)
  exact halfSpaceSecondOrderExtension_jets he hT (boundaryTraceLayer e B)
    (boundaryTraceGradient e B) (boundaryTraceHessian e B) (boundaryTraceTimeJet e B)
    (boundaryTraceLayer_continuousOn hα hT hT1 e hB hPast)
    (boundaryTraceGradient_continuousOn hα hT hT1 he hB hPast)
    (holderBound_continuousOn hα (hHH e he T hT1 B F hB))
    (holderBound_continuousOn hα (hTT e he T hT1 B F hB))
    (fun p hp => boundaryTraceLayer_hasFDerivAt_gradient he hc hb hp.2.1 hp.1)
    (fun p hp => boundaryTraceGradient_hasFDerivAt_hessian hα he hc hb hB.1 hh hp.2.1 hPast hp.1)
    (fun p hp => normalTraceLayer_hasDerivWithinAt_time_closed hα hα1 hT hT1 hB hPast hp.1 hp.2
      (halfSpaceBoundaryProjection e p.1))

/-- A uniform full Schauder estimate for the actual extended trace layer.
Only the original Holder source and zero initial corner compatibility enter;
no regularity of the desired solution or its jets is assumed. -/
theorem boundaryTraceLayer_extension_schauder {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ T, 0 < T → T ≤ 1 →
      ∀ (B : Point n → ℝ) F, HolderBound α univ B F →
      (∀ y s, s ≤ 0 → B (y,s) = 0) →
      SchauderBound α (cylinder univ 0 T)
        (halfSpaceSecondOrderExtension e (boundaryTraceLayer e B)) (C*F) := by
  obtain ⟨CG,hCG,hG⟩ := boundaryTraceGradient_bound (n := n)
  obtain ⟨CH,hCH,hHH⟩ := boundaryTraceHessian_holder (n := n) hα hα1
  obtain ⟨Ct,hCt,hTT⟩ := boundaryTraceTimeJet_holder (n := n) hα hα1
  obtain ⟨CE,hCE,hExt⟩ := halfSpaceSecondOrderExtension_schauder (n := n) hα hα1
  refine ⟨CE*(1+CG+CH+Ct),by positivity,?_⟩
  intro e he T hT hT1 B F hB hPast
  let Q := cylinder {x | 0 ≤ inner ℝ e x} 0 T
  let K := (1+CG+CH+Ct)*F
  have hF : 0 ≤ F := hB.1
  have hc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hb : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (mem_univ _)
  have hFK : F ≤ K := by dsimp [K]; nlinarith
  have hGK : CG*F ≤ K := by dsimp [K]; nlinarith
  have hHK : CH*F ≤ K := by dsimp [K]; nlinarith
  have htK : Ct*F ≤ K := by dsimp [K]; nlinarith
  have hH : HolderBound α Q (boundaryTraceHessian e B) K :=
    holderBound_mono_const (hHH e he T hT1 B F hB) hHK
  have hTime : HolderBound α Q (boundaryTraceTimeJet e B) K :=
    holderBound_mono_const (hTT e he T hT1 B F hB) htK
  have hLow : ∀ p ∈ Q, |boundaryTraceLayer e B p| ≤ K ∧ ‖boundaryTraceGradient e B p‖ ≤ K := by
    intro p hp
    constructor
    · exact ((normalTraceLayer_integrable_and_bound hc hb hp.2.1 hp.1
        (halfSpaceBoundaryProjection e p.1)).2.trans
        (mul_le_of_le_one_left hF (hp.2.2.trans hT1))).trans hFK
    · have hPow : p.2^(1/2 : ℝ) ≤ 1 := by
        simpa only [Real.one_rpow] using
          Real.rpow_le_rpow hp.2.1 (hp.2.2.trans hT1) (by norm_num : (0 : ℝ) ≤ 1/2)
      exact ((hG e he B F hc hb p.2 hp.2.1 p.1 hp.1).trans
        (mul_le_of_le_one_right (by positivity) hPow)).trans hGK
  have hh : ∀ s x y, |B (x,s)-B (y,s)| ≤ F*‖x-y‖^α := by
    intro s x y
    simpa only [holderWeight,sub_self,abs_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),
      add_zero,Real.norm_eq_abs] using hB.2.2 (x,s) (mem_univ _) (y,s) (mem_univ _)
  have h := hExt e T (boundaryTraceLayer e B) (boundaryTraceGradient e B)
    (boundaryTraceHessian e B) (boundaryTraceTimeJet e B) K he hT
    (boundaryTraceLayer_continuousOn hα hT hT1 e hB hPast)
    (boundaryTraceGradient_continuousOn hα hT hT1 he hB hPast)
    (holderBound_continuousOn hα hH) (holderBound_continuousOn hα hTime)
    (fun p hp => boundaryTraceLayer_hasFDerivAt_gradient he hc hb hp.2.1 hp.1)
    (fun p hp => boundaryTraceGradient_hasFDerivAt_hessian hα he hc hb hF hh hp.2.1 hPast hp.1)
    (fun p hp => normalTraceLayer_hasDerivWithinAt_time_closed hα hα1 hT hT1 hB hPast hp.1 hp.2
      (halfSpaceBoundaryProjection e p.1)) (hF.trans hFK) hLow hH hTime
  convert h using 1
  dsimp only [K]
  ring

end Yau.LeafProofs.L16Aux
