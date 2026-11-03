import Yau.Proofs.P06LocalCauchyLimitForms
import Yau.LeafProofs.L03HodgeJets

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.LocalCauchyLimit
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

section Slice
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem slice_iteratedFDeriv {f : E × ℝ → F} {S : Set (E × ℝ)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) {z : E} {t : ℝ} (hp : (z,t) ∈ S) (m : ℕ) :
    iteratedFDeriv ℝ m (fun w => f (w,t)) z =
      (iteratedFDeriv ℝ m f (z,t)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E ℝ) := by
  let O := (fun p : E × ℝ => p+(0,t)) ⁻¹' S
  have hO : IsOpen O := hS.preimage (continuous_id.add continuous_const)
  have hshift : ContDiffOn ℝ ∞ (fun p : E × ℝ => f (p+(0,t))) O :=
    hf.comp (contDiff_id.add contDiff_const).contDiffOn (fun p hp => hp)
  let L := ContinuousLinearMap.inl ℝ E ℝ
  have hL : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have hz : L z ∈ O := by
    change (z,0)+(0,t) ∈ S
    simpa only [Prod.mk_add_mk,add_zero,zero_add] using hp
  have h := L.iteratedFDerivWithin_comp_right hshift hO.uniqueDiffOn hL.uniqueDiffOn hz
    (i := m) (by simp)
  rw [iteratedFDerivWithin_of_isOpen m hL hz,iteratedFDerivWithin_of_isOpen m hO hz] at h
  rw [iteratedFDeriv_comp_add_right] at h
  simpa only [Function.comp_def,L,ContinuousLinearMap.inl_apply,Prod.mk_add_mk,
    add_zero,zero_add] using h

def secondCurry : (E [×2]→L[ℝ] F) →L[ℝ] E →L[ℝ] E →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E (E [×1]→L[ℝ] F) (E →L[ℝ] F)
    (continuousMultilinearCurryFin1 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) F).toContinuousLinearEquiv.toContinuousLinearMap

theorem firstCurry_actual (f : E → F) (z : E) :
    continuousMultilinearCurryFin1 ℝ E F (iteratedFDeriv ℝ 1 f z) = fderiv ℝ f z := by
  ext v
  change iteratedFDeriv ℝ 1 f z (Fin.snoc 0 v) = fderiv ℝ f z v
  rw [iteratedFDeriv_one_apply]
  rfl

theorem secondCurry_actual (f : E → F) (z : E) :
    secondCurry (iteratedFDeriv ℝ 2 f z) = fderiv ℝ (fderiv ℝ f) z := by
  ext v w
  change iteratedFDeriv ℝ 2 f z (Fin.cons v (Fin.snoc 0 w)) = fderiv ℝ (fderiv ℝ f) z v w
  rw [iteratedFDeriv_two_apply]
  rfl

end Slice

theorem jointJet_tendsto (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hU : SmoothFormTime U (Ioi 0))
    (hl : JointJetLimit Us U) (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (t : ℝ) (ht : 0 < t) (I : Fin k → RIdx n) (m : ℕ) :
    Tendsto (fun j => iteratedFDeriv ℝ m
      (fun p : ComplexVector n × ℝ => formComponents (Us j p.2) x p.1 I) (z,t)) atTop
      (𝓝 (iteratedFDeriv ℝ m (fun p : ComplexVector n × ℝ => formComponents (U p.2) x p.1 I) (z,t))) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨N,hN⟩ := hl x {z} isCompact_singleton (by simpa using hz)
    (t/2) (t+1) (half_pos ht) (by linarith) m I η hη
  refine ⟨N,fun j hj => ?_⟩
  have hb := hN j hj z (mem_singleton z) t ⟨by linarith,by linarith⟩
  change ‖iteratedFDeriv ℝ m
    ((fun p : ComplexVector n × ℝ => formComponents (Us j p.2) x p.1 I) -
     (fun p : ComplexVector n × ℝ => formComponents (U p.2) x p.1 I)) (z,t)‖ < η at hb
  have hp : (z,t) ∈ chartTarget x ×ˢ Ioi 0 := ⟨hz,ht⟩
  have hop := (isOpen_extChartAt_target (I := ComplexModel n) x).prod (isOpen_Ioi (a := (0 : ℝ)))
  rw [iteratedFDeriv_sub_apply (i := m)
    (((hUs j x I).contDiffAt (hop.mem_nhds hp)).of_le (by simp))
    (((hU x I).contDiffAt (hop.mem_nhds hp)).of_le (by simp))] at hb
  simpa only [dist_eq_norm] using hb

def modelJetLift (m : ℕ) :
    ((Fin k → RIdx n) → (ComplexVector n × ℝ) [×m]→L[ℝ] ℝ) →L[ℝ]
      (ComplexVector n × ℝ) [×m]→L[ℝ] HodgeJets.Fiber n k := by
  let P : ((Fin k → RIdx n) → (ComplexVector n × ℝ) [×m]→L[ℝ] ℝ) ≃ₗᵢ[ℝ]
      (ComplexVector n × ℝ) [×m]→L[ℝ] ((Fin k → RIdx n) → ℝ) :=
    ContinuousMultilinearMap.piₗᵢ ℝ (fun _ : Fin m => ComplexVector n × ℝ)
  exact (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin m => ComplexVector n × ℝ) _ _ (modelFormReconstruction n k)).comp
      P.toContinuousLinearEquiv.toContinuousLinearMap

theorem modelJetLift_actual (m : ℕ) (f : ComplexVector n × ℝ → HodgeJets.Fiber n k)
    (p : ComplexVector n × ℝ) (hf : ContDiffAt ℝ ∞ f p) :
    modelJetLift m (fun I => iteratedFDeriv ℝ m (fun q => f q (fun r => realVec (I r))) p) =
      iteratedFDeriv ℝ m f p := by
  apply ContinuousMultilinearMap.ext
  intro v
  change modelFormReconstruction n k
    (fun I => iteratedFDeriv ℝ m (fun q => f q (fun r => realVec (I r))) p v) = _
  have he : (fun I => iteratedFDeriv ℝ m (fun q => f q (fun r => realVec (I r))) p v) =
      modelFormCoefficientMap n k (iteratedFDeriv ℝ m f p v) := by
    funext I
    let C := ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))
    exact congrArg (fun D => D v) (C.iteratedFDeriv_comp_left hf (i := m) (by simp))
  rw [he,modelFormReconstruction_coefficient]

theorem jointModelJet_tendsto (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hUs : ∀ j, SmoothFormTime (Us j) (Ioi 0)) (hU : SmoothFormTime U (Ioi 0))
    (hl : JointJetLimit Us U) (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (t : ℝ) (ht : 0 < t) (m : ℕ) :
    Tendsto (fun j => iteratedFDeriv ℝ m
      (fun p : ComplexVector n × ℝ => chartForm (Us j p.2) x p.1) (z,t)) atTop
      (𝓝 (iteratedFDeriv ℝ m (fun p : ComplexVector n × ℝ => chartForm (U p.2) x p.1) (z,t))) := by
  have hpi := tendsto_pi_nhds.mpr (fun I => jointJet_tendsto Us U hUs hU hl x z hz t ht I m)
  have h := ((modelJetLift (n := n) (k := k) m).continuous.tendsto _).comp hpi
  have hAt (V : ℝ → RealForm M k) (hV : SmoothFormTime V (Ioi 0)) :
      ContDiffAt ℝ ∞ (fun p : ComplexVector n × ℝ => chartForm (V p.2) x p.1) (z,t) :=
    ((modelForm_contDiffOn_iff _ _).mpr (fun I => hV x I)).contDiffAt
      (((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi).mem_nhds ⟨hz,ht⟩)
  convert h using 1
  · funext j
    exact (modelJetLift_actual m _ _ (hAt (Us j) (hUs j))).symm
  · exact congrArg nhds (modelJetLift_actual m _ _ (hAt U hU)).symm

end Yau.NodeProofs.P06Aux.LocalCauchyLimit
