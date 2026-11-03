import Yau.Proofs.F05JetExtensionBounds
import Yau.LeafProofs.L16ChartLowJetTransport

/-! The actual local jets have lower-order Holder control on an inner
physical buffer. No mixed derivatives or prior lower Holder norm is assumed. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_local_inner_low_holder (A : AtlasData M) (i : Fin A.count) :
    ∃ E : ℝ, 0 < E ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ) (hT : 0 < T)
      (u : F05LocalFTCGraph A i α hT.le),
      HolderBound α (cylinder (F05D A i ∩ Metric.closedBall 0 (1/3)) 0 T)
        (fun p => (F05BCFFun u.val.1 p,F05BCFFun u.val.2.1 p)) (E*‖u.val‖) := by
  let η : Space n → ℝ := innerPatchBump (1/2) (by norm_num) 0
  have hη : ContDiff ℝ ∞ η := innerPatchBump_contDiff (by norm_num) 0
  have hSupport : tsupport η ⊆ Metric.closedBall 0 1 := by
    rw [(innerPatchBump (1/2) (by norm_num) (0 : Space n)).tsupport_eq]
    change Metric.closedBall 0 (3*(1/2 : ℝ)/2) ⊆ Metric.closedBall 0 1
    exact Metric.closedBall_subset_closedBall (by norm_num)
  obtain ⟨E,hE,hBudget⟩ := F05_local_extension_raw_low_budget A i η hη hSupport
  refine ⟨E,hE,?_⟩
  intro α hα hα1 T hT u
  have hLow := (hBudget α hα hα1 T hT u).2.2
  have hSmall := holderBound_mono hLow
    (show cylinder (F05D A i ∩ Metric.closedBall 0 (1/3)) 0 T ⊆ cylinder univ 0 T from
      fun p hp => ⟨mem_univ _,hp.2⟩)
  have hJets := F05_local_extension_jets A i α hT u η hη hSupport
  apply holderBound_congr_on hSmall
  intro p hp
  have hpQ : p ∈ cylinder (closure (F05ModelOpen A i)) 0 T :=
    ⟨F05D_subset_model_closure A i hp.1.1,hp.2⟩
  have hn : ‖p.1‖ ≤ 1/3 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1.2
  have hPlateau : η =ᶠ[𝓝 p.1] (fun _ => 1) := by
    apply innerPatchBump_eventually_one_of_norm_lt (by norm_num)
    rw [sub_zero]
    exact hn.trans_lt (by norm_num)
  have hηVal : η p.1 = 1 := hPlateau.eq_of_nhds
  have hηD : fderiv ℝ η p.1 = 0 := by
    simpa only [fderiv_fun_const,Pi.zero_apply] using hPlateau.fderiv_eq (𝕜 := ℝ)
  change (F05LocalJetExtension A i η u.val p,spatialD (F05LocalJetExtension A i η u.val) p) =
    (F05BCFFun u.val.1 p,F05BCFFun u.val.2.1 p)
  apply Prod.ext
  · rw [hJets.2.1 hpQ]
    simp only [F05CutoffJetValue,hηVal,one_mul]
  · rw [hJets.2.2.1 hpQ]
    simp only [F05CutoffJetGradient,hηVal,hηD,one_smul,smul_zero,add_zero]

end Yau.Proofs.F05Aux
