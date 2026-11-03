import Yau.Proofs.F05CompactHolder
import Yau.Proofs.F05SmallTime

/-! An actual smooth fixed source vanishing on the initial slice has a
uniform small Holder norm on shrinking time slabs, in the original norm. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_compact_cylinder_holder_zero {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {U K : Set (Space n)}
    (hU : IsOpen U) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ U)
    {S : ℝ} (hS : 0 < S) {f : Point n → V}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Icc 0 S)) (h0 : ∀ x ∈ K, f (x,0) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ), 0 < T → T ≤ S → T ≤ 1 →
      HolderBound α (cylinder K 0 T) f (C*T^((1-α)/2)) := by
  let Q := U ×ˢ Icc 0 S
  let B := K ×ˢ Icc 0 S
  have hSub : B ⊆ Q := fun p hp => ⟨hKU hp.1,hp.2⟩
  have hUnique : UniqueDiffOn ℝ Q := hU.uniqueDiffOn.prod (uniqueDiffOn_Icc hS)
  have hDerivative := hf.continuousOn_fderivWithin hUnique (by simp)
  obtain ⟨D,hD⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn (hDerivative.mono hSub)
  let L := 1+|D|
  have hL : 0 < L := by dsimp only [L]; positivity
  have hDL : D ≤ L := by dsimp only [L]; linarith [le_abs_self D]
  have hLip (p q : Point n) (hp : p ∈ B) (hq : q ∈ B) : ‖f p-f q‖ ≤ L*‖p-q‖ := by
    apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (s := B) (f' := fderivWithin ℝ f Q)
      (fun z hz => ((hf.differentiableOn (by simp) z (hSub hz)).hasFDerivWithinAt).mono hSub)
      (fun z hz => (hD z hz).trans hDL) (hConv.prod (convex_Icc _ _)) hq hp
  refine ⟨2*L,by positivity,?_⟩
  intro α hα hα1 T hT hTS hT1
  obtain ⟨hρ,hρ1,hScale,hPower⟩ := F05_sqrt_scale hT hT1 α
  have hTime : Icc (0 : ℝ) T ⊆ Icc 0 S := fun t ht => ⟨ht.1,ht.2.trans hTS⟩
  have hTroot : T ≤ Real.sqrt T := by nlinarith [Real.sq_sqrt hT.le]
  have hValue (p : Point n) (hp : p ∈ cylinder K 0 T) : ‖f p‖ ≤ L*Real.sqrt T := by
    have hh := hLip p (p.1,0) ⟨hp.1,hTime hp.2⟩ ⟨hp.1,le_rfl,hS.le⟩
    rw [h0 p.1 hp.1,sub_zero] at hh
    have hNorm : ‖p-(p.1,0)‖ = p.2 := by
      simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,sub_zero,norm_zero,Real.norm_eq_abs,
        abs_of_nonneg hp.2.1,max_eq_right hp.2.1]
    rw [hNorm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hp.2.2.trans hTroot) hL.le)
  have hSpace (x y : Space n) (t : ℝ) (hx : x ∈ K) (hy : y ∈ K) (ht : t ∈ Icc 0 T) :
      ‖f (x,t)-f (y,t)‖ ≤ L*‖x-y‖ := by
    simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,max_eq_left (norm_nonneg _)] using
      hLip (x,t) (y,t) ⟨hx,hTime ht⟩ ⟨hy,hTime ht⟩
  have hTimeLip (x : Space n) (s t : ℝ) (hx : x ∈ K) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
      ‖f (x,s)-f (x,t)‖ ≤ L*Real.sqrt |s-t| := by
    have hh : ‖f (x,s)-f (x,t)‖ ≤ L*|s-t| := by
      simpa [Prod.norm_def] using hLip (x,s) (x,t) ⟨hx,hTime hs⟩ ⟨hx,hTime ht⟩
    have hAbs : |s-t| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith [hs.2,ht.1],by linarith [ht.2,hs.1]⟩
    have hRoot : |s-t| ≤ Real.sqrt |s-t| := by
      nlinarith [Real.sq_sqrt (abs_nonneg (s-t)),Real.sqrt_nonneg |s-t|,Real.sqrt_le_one.mpr hAbs]
    exact hh.trans (mul_le_mul_of_nonneg_left hRoot hL.le)
  have hBound := holderBound_of_small_parabolic_lipschitz hα hα1 hρ hρ1 hL.le hValue hSpace hTimeLip
  rwa [hPower] at hBound

end Yau.Proofs.F05Aux
