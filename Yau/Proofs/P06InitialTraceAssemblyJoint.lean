import Yau.Proofs.P06InitialTraceAssemblySpatial
import Yau.Proofs.P06LocalCauchyLimitJetMaps

/-! Restrict the actual positive-time joint jets to spatial slices. The unused
zeroth cutoff is removed by reindexing, so no regularity of it is assumed. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P06Aux.InitialTrace
open Yau Yau.Blueprint
variable {n k : ℕ} {M : ComplexManifold n}

theorem spatial_jet_norm_le_joint_jet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {S : Set (E × ℝ)} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) {z : E} {t : ℝ} (hp : (z, t) ∈ S) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun w => f (w, t)) z‖ ≤ ‖iteratedFDeriv ℝ m f (z, t)‖ := by
  rw [LocalCauchyLimit.slice_iteratedFDeriv hS hf hp m]
  have hL : ‖ContinuousLinearMap.inl ℝ E ℝ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simp
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  exact mul_le_of_le_one_right (norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL))

theorem smoothFormTime_spatial_slice (U : ℝ → RealForm M k)
    (hU : SmoothFormTime U (Ioi 0)) {t : ℝ} (ht : 0 < t) : SmoothRealForm (U t) := by
  intro x I
  exact (hU x I).comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)

theorem spatialJetLimit_of_jointJetLimit
    (Us : ℕ → ℝ → RealForm M k) (U : ℝ → RealForm M k)
    (hUs : ∀ l, 1 ≤ l → SmoothFormTime (Us l) (Ioi 0))
    (hU : SmoothFormTime U (Ioi 0)) (hlim : LocalCauchyLimit.JointJetLimit Us U) :
    SpatialJetLimit Us U := by
  have hshift : LocalCauchyLimit.JointJetLimit (fun j => Us (j + 1)) U := by
    intro x K hK hKO eps T heps heT m I η hη
    obtain ⟨N, hN⟩ := hlim x K hK hKO eps T heps heT m I η hη
    exact ⟨N, fun j hj => hN (j + 1) (by omega)⟩
  intro x z hz t ht m I
  have hh := LocalCauchyLimit.jointJet_tendsto (fun j => Us (j + 1)) U
    (fun j => hUs (j + 1) (by omega)) hU hshift x z hz t ht I m
  let P : ((ComplexVector n × ℝ) [×m]→L[ℝ] ℝ) →L[ℝ]
      (ComplexVector n) [×m]→L[ℝ] ℝ :=
    ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin m => ContinuousLinearMap.inl ℝ (ComplexVector n) ℝ)
  have hP := (P.continuous.tendsto _).comp hh
  have hs (V : ℝ → RealForm M k) (hV : SmoothFormTime V (Ioi 0)) :
      iteratedFDeriv ℝ m (fun w => formComponents (V t) x w I) z =
        P (iteratedFDeriv ℝ m
          (fun p : ComplexVector n × ℝ => formComponents (V p.2) x p.1 I) (z, t)) := by
    exact LocalCauchyLimit.slice_iteratedFDeriv
      ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi)
      (hV x I) ⟨hz, ht⟩ m
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert hP using 1
  · funext l
    exact hs (Us (l + 1)) (hUs (l + 1) (by omega))
  · exact congrArg nhds (hs U hU)

end Yau.NodeProofs.P06Aux.InitialTrace
