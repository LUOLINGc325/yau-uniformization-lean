import Yau.Proofs.F05JetLowHolder
import Yau.Proofs.F05JetCutoffHolder
import Yau.Proofs.F05SpatialCutoffHolder

/-! Original high Holder components and actual lower-jet interpolation give
the high Holder budget of the concrete cutoff on the entire physical model. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_physHolderDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_physHolderDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_physHolderHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_physHolderHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

theorem F05_inner_model_cylinder (A : AtlasData M) (i : Fin A.count) (T : ℝ) :
    ((Metric.closedBall (0 : Space n) (1/3)) ×ˢ (univ : Set ℝ)) ∩
      cylinder (closure (F05ModelOpen A i)) 0 T =
    cylinder (F05D A i ∩ Metric.closedBall 0 (1/3)) 0 T := by
  ext p
  constructor
  · intro hp
    have hn : ‖p.1‖ ≤ 1/3 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hp.1.1
    have hFace := hp.2.1
    rw [F05ModelOpen_eq,F05FlatOpen_closure] at hFace
    exact ⟨⟨⟨hn.trans (by norm_num),hFace⟩,hp.1.1⟩,hp.2.2⟩
  · intro hp
    exact ⟨⟨hp.1.2,mem_univ _⟩,F05D_subset_model_closure A i hp.1.1,hp.2⟩

theorem F05_local_cutoff_high_budget (A : AtlasData M) (i : Fin A.count)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hSupport : tsupport φ ⊆ Metric.closedBall 0 (1/4)) :
    ∃ E : ℝ, 0 < E ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ) (hT : 0 < T)
      (u : F05LocalFTCGraph A i α hT.le),
      HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T)
        (F05CutoffJetHessian φ u.val) (E*‖u.val‖) ∧
      HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T)
        (F05CutoffJetTime φ u.val) (E*‖u.val‖) := by
  have hc : HasCompactSupport φ :=
    (isCompact_closedBall (0 : Space n) (1/4)).of_isClosed_subset (isClosed_tsupport φ) hSupport
  obtain ⟨P,hP,hCoeff⟩ := F05_smooth_cutoff_three_holder hφ hc
  obtain ⟨L,hL,hLow⟩ := F05_local_inner_low_holder A i
  refine ⟨8*P*(1+L),by positivity,?_⟩
  intro α hα hα1 T hT u
  let U := (Metric.closedBall (0 : Space n) (1/3)) ×ˢ (univ : Set ℝ)
  let Q := cylinder (closure (F05ModelOpen A i)) 0 T
  have hInner : U∩Q = cylinder (F05D A i ∩ Metric.closedBall 0 (1/3)) 0 T :=
    F05_inner_model_cylinder A i T
  have hSub : U∩Q ⊆ F05Q A i T := by
    rw [hInner]
    exact fun p hp => ⟨hp.1.1,hp.2⟩
  have hNorm : 0 ≤ ‖u.val‖ := norm_nonneg _
  have hScaleLow : L*‖u.val‖ ≤ (1+L)*‖u.val‖ := by nlinarith
  have hScaleHigh : ‖u.val‖ ≤ (1+L)*‖u.val‖ := by nlinarith
  have hPair : HolderBound α (U∩Q)
      (fun p => (F05BCFFun u.val.1 p,F05BCFFun u.val.2.1 p)) (L*‖u.val‖) := by
    rw [hInner]
    exact hLow α hα hα1 T hT u
  have hV : HolderBound α (U∩Q) (F05BCFFun u.val.1) ((1+L)*‖u.val‖) := by
    apply holderBound_mono_const _ hScaleLow
    refine ⟨hPair.1,fun p hp => (le_max_left _ _).trans (hPair.2.1 p hp),?_⟩
    intro p hp q hq
    exact (le_max_left _ _).trans (hPair.2.2 p hp q hq)
  have hG : HolderBound α (U∩Q) (F05BCFFun u.val.2.1) ((1+L)*‖u.val‖) := by
    apply holderBound_mono_const _ hScaleLow
    refine ⟨hPair.1,fun p hp => (le_max_right _ _).trans (hPair.2.1 p hp),?_⟩
    intro p hp q hq
    exact (le_max_right _ _).trans (hPair.2.2 p hp q hq)
  have hH := holderBound_mono_const (holderBound_mono
    (F05JetComponent_hessian_holderBound u.val) hSub) hScaleHigh
  have hTime := holderBound_mono_const (holderBound_mono
    (F05JetComponent_time_holderBound u.val) hSub) hScaleHigh
  have hφC := hCoeff α hα hα1
  have hOutside : ∀ p ∈ Q, p ∉ U → φ p.1 = 0 ∧ fderiv ℝ φ p.1 = 0 ∧
      fderiv ℝ (fderiv ℝ φ) p.1 = 0 := by
    intro p _ hp
    have hOut : p.1 ∉ tsupport φ := by
      intro h
      exact hp ⟨Metric.closedBall_subset_closedBall (by norm_num : (1/4 : ℝ) ≤ 1/3) (hSupport h),mem_univ _⟩
    exact ⟨image_eq_zero_of_notMem_tsupport hOut,fderiv_of_notMem_tsupport (𝕜 := ℝ) hOut,
      fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hOut (tsupport_fderiv_subset ℝ h))⟩
  have hResult := F05_cutoff_jet_high_holder φ u.val
    (holderBound_mono hφC.1 (subset_univ Q))
    (holderBound_mono hφC.2.1 (subset_univ Q))
    (holderBound_mono hφC.2.2 (subset_univ Q)) hV hG hH hTime hOutside
  have hBudget : 8*P*((1+L)*‖u.val‖) = (8*P*(1+L))*‖u.val‖ := by ring
  rw [hBudget] at hResult
  exact hResult

end Yau.Proofs.F05Aux
