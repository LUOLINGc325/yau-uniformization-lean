import Yau.LeafProofs.L17SmallTranslationFullJacobian

open Set Metric Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SmallTranslationAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (L : ℝ) (hL : 0 ≤ L)
    (hDf : ∀ z, ‖fderiv ℝ χ z‖ ≤ L)

theorem cutoffInverse_joint_contDiffAt {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) (y : E) :
    ContDiffAt ℝ ∞ (fun p : E × E => cutoffInverse χ hχ L hL hDf p.1 p.2) (θ,y) := by
  let z := cutoffInverse χ hχ L hL hDf θ y
  let J := cutoffFullJacobianEquiv χ L hL hDf θ hθ z
  have hf : ContDiffAt ℝ ∞ (cutoffFullMap χ) (θ,z) := (cutoffFullMap_contDiff hχ).contDiffAt
  have hJac : HasFDerivAt (cutoffFullMap χ) J.toContinuousLinearMap (θ,z) :=
    cutoffFullMap_hasFDerivAt hχ hL hDf hθ z
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let e := hf.toOpenPartialHomeomorph (f' := J) (cutoffFullMap χ) hJac hn
  let l := hf.localInverse (f' := J) hJac hn
  have hImage : cutoffFullMap χ (θ,z)=(θ,y) :=
    Prod.ext rfl (cutoffTranslation_inverse χ hχ L hL hDf hθ y)
  have hSmooth : ContDiffAt ℝ ∞ l (θ,y) := by
    have h := hf.to_localInverse (f' := J) hJac hn
    rw [hImage] at h
    exact h
  have hTarget : (θ,y) ∈ e.target := by
    have h := hf.image_mem_toOpenPartialHomeomorph_target (f' := J) hJac hn
    rw [hImage] at h
    exact h
  have hθball : θ ∈ ball (0 : E) (smallTranslationRadius L) := by
    simpa only [mem_ball,dist_zero_right] using hθ
  have hEq : (fun p : E × E => cutoffInverse χ hχ L hL hDf p.1 p.2) =ᶠ[𝓝 (θ,y)]
      (fun p => (l p).2) := by
    filter_upwards [e.open_target.mem_nhds hTarget,
      (isOpen_ball.prod isOpen_univ).mem_nhds (show (θ,y) ∈
        ball (0 : E) (smallTranslationRadius L) ×ˢ (Set.univ : Set E) from ⟨hθball,mem_univ _⟩)] with p hpT hpSmall
    have hInv : cutoffFullMap χ (l p)=p := by
      have h := e.right_inv hpT
      exact h
    have hFirst := congrArg Prod.fst hInv
    change (l p).1=p.1 at hFirst
    have hSecond := congrArg Prod.snd hInv
    change cutoffTranslation χ (l p).1 (l p).2=p.2 at hSecond
    rw [hFirst] at hSecond
    have hpθ : ‖p.1‖ < smallTranslationRadius L := by
      simpa only [mem_ball,dist_zero_right] using hpSmall.1
    have h := cutoffInverse_translation χ hχ L hL hDf hpθ (l p).2
    rw [hSecond] at h
    exact h
  exact hSmooth.snd.congr_of_eventuallyEq hEq

theorem cutoffInverse_joint_contDiffOn :
    ContDiffOn ℝ ∞ (fun p : E × E => cutoffInverse χ hχ L hL hDf p.1 p.2)
      (ball (0 : E) (smallTranslationRadius L) ×ˢ (Set.univ : Set E)) := by
  intro p hp
  exact (cutoffInverse_joint_contDiffAt χ hχ L hL hDf
    (by simpa only [mem_ball,dist_zero_right] using hp.1) p.2).contDiffWithinAt

theorem cutoffInverse_contDiff {θ : E} (hθ : ‖θ‖ < smallTranslationRadius L) :
    ContDiff ℝ ∞ (cutoffInverse χ hχ L hL hDf θ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  exact (cutoffInverse_joint_contDiffAt χ hχ L hL hDf hθ y).comp y
    (contDiffAt_const.prodMk contDiffAt_id)

end Yau.LeafProofs.L17SmallTranslationAux
