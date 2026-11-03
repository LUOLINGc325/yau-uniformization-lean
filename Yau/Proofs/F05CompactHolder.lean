import Yau.LeafProofs.L16LowJetInterpolation

/-! Actual smooth fields have a fixed parabolic Holder budget on a compact
convex spatial buffer, before the exponent and moving endpoint are chosen. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_compact_cylinder_holder {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {U K : Set (Space n)}
    (hU : IsOpen U) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ U)
    {S : ℝ} (hS : 0 < S) {f : Point n → V}
    (hf : ContDiffOn ℝ ∞ f (cylinder U 0 S)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ), T ≤ S →
      HolderBound α (cylinder K 0 T) f C := by
  let Q := cylinder U 0 S
  let B := cylinder K 0 S
  have hSub : B ⊆ Q := fun p hp => ⟨hKU hp.1,hp.2⟩
  have hUnique : UniqueDiffOn ℝ Q := hU.uniqueDiffOn.prod (uniqueDiffOn_Icc hS)
  have hDerivative := hf.continuousOn_fderivWithin hUnique (by simp)
  have hB : IsCompact B := hK.prod isCompact_Icc
  obtain ⟨A,hA⟩ := hB.exists_bound_of_continuousOn (hf.continuousOn.mono hSub)
  obtain ⟨D,hD⟩ := hB.exists_bound_of_continuousOn (hDerivative.mono hSub)
  let L := 1+|A|+|D|
  have hL : 0 < L := by dsimp only [L]; positivity
  have hAL : A ≤ L := by dsimp only [L]; linarith [le_abs_self A,abs_nonneg D]
  have hDL : D ≤ L := by dsimp only [L]; linarith [le_abs_self D,abs_nonneg A]
  have hValue : ∀ p ∈ B, ‖f p‖ ≤ L := fun p hp => (hA p hp).trans hAL
  have hLip (p q : Point n) (hp : p ∈ B) (hq : q ∈ B) : ‖f p-f q‖ ≤ L*‖p-q‖ := by
    apply Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (s := B) (f' := fderivWithin ℝ f Q)
      (fun z hz => ((hf.differentiableOn (by simp) z (hSub hz)).hasFDerivWithinAt).mono hSub)
      (fun z hz => (hD z hz).trans hDL) (hConv.prod (convex_Icc _ _)) hq hp
  let E := L*(1+S)
  have hE : 0 < E := by dsimp only [E]; positivity
  have hLE : L ≤ E := by dsimp only [E]; nlinarith
  refine ⟨2*E,by positivity,?_⟩
  intro α hα hα1 T hTS
  have hTimeSub : Icc (0 : ℝ) T ⊆ Icc 0 S := fun t ht => ⟨ht.1,ht.2.trans hTS⟩
  have hBound (p : Point n) (hp : p ∈ cylinder K 0 T) : ‖f p‖ ≤ E*1 := by
    rw [mul_one]
    exact (hValue p ⟨hp.1,hTimeSub hp.2⟩).trans hLE
  have hSpace (x y : Space n) (t : ℝ) (hx : x ∈ K) (hy : y ∈ K) (ht : t ∈ Icc 0 T) :
      ‖f (x,t)-f (y,t)‖ ≤ E*‖x-y‖ := by
    have h := hLip (x,t) (y,t) ⟨hx,hTimeSub ht⟩ ⟨hy,hTimeSub ht⟩
    have h' : ‖f (x,t)-f (y,t)‖ ≤ L*‖x-y‖ := by simpa [Prod.norm_def] using h
    exact h'.trans (mul_le_mul_of_nonneg_right hLE (norm_nonneg _))
  have hTime (x : Space n) (s t : ℝ) (hx : x ∈ K) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
      ‖f (x,s)-f (x,t)‖ ≤ E*Real.sqrt |s-t| := by
    have hsS := hTimeSub hs
    have htS := hTimeSub ht
    have h := hLip (x,s) (x,t) ⟨hx,hsS⟩ ⟨hx,htS⟩
    have h' : ‖f (x,s)-f (x,t)‖ ≤ L*|s-t| := by simpa [Prod.norm_def] using h
    have hAbs : |s-t| ≤ S := abs_sub_le_iff.mpr ⟨by linarith [hsS.1,hsS.2,htS.1,htS.2],by linarith [hsS.1,hsS.2,htS.1,htS.2]⟩
    have hRoot : Real.sqrt |s-t| ≤ 1+S := by
      nlinarith [Real.sq_sqrt (abs_nonneg (s-t)),Real.sqrt_nonneg |s-t|]
    have hScale : |s-t| ≤ (1+S)*Real.sqrt |s-t| := by
      calc
        |s-t| = (Real.sqrt |s-t|)^2 := (Real.sq_sqrt (abs_nonneg (s-t))).symm
        _ ≤ (1+S)*Real.sqrt |s-t| := by
          simpa only [pow_two] using mul_le_mul_of_nonneg_right hRoot (Real.sqrt_nonneg |s-t|)
    calc
      _ ≤ L*|s-t| := h'
      _ ≤ L*((1+S)*Real.sqrt |s-t|) := mul_le_mul_of_nonneg_left hScale hL.le
      _ = E*Real.sqrt |s-t| := by dsimp only [E]; ring
  have h := holderBound_of_small_parabolic_lipschitz hα hα1 (ρ := 1) (by norm_num)
    (by norm_num) hE.le hBound hSpace hTime
  simpa only [Real.one_rpow,mul_one] using h

end Yau.Proofs.F05Aux
