import Yau.Proofs.F04TimeGlue

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem negativeJet_zero_curry (O : Set E) (χ : ℝ → ℝ) (f : E × ℝ → F) (p : E × ℝ) :
    (negativeJet O χ f 0 p).curry0 =
      ∑' k, seeleyWeight k • positiveCutoff χ f (reflectLinear k p) := by
  change (continuousMultilinearCurryFin0 ℝ (E × ℝ) F) (negativeJet O χ f 0 p) = _
  unfold negativeJet
  calc
    _ = ∑' k, (continuousMultilinearCurryFin0 ℝ (E × ℝ) F)
        (seeleyWeight k •
          (iteratedFDerivWithin ℝ 0 (positiveCutoff χ f) (O ×ˢ Ici 0) (reflectLinear k p)).compContinuousLinearMap
            (fun _ : Fin 0 => reflectLinear k)) :=
      (continuousMultilinearCurryFin0 ℝ (E × ℝ) F).toContinuousLinearEquiv.map_tsum
    _ = _ := ?_
  apply tsum_congr
  intro k
  simp only [map_smul, continuousMultilinearCurryFin0_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
    continuousMultilinearCurryFin0_symm_apply, ContinuousMultilinearMap.uncurry0_apply]

def gluedJet (O : Set E) (S : ℝ) (χ : ℝ → ℝ) (f : E × ℝ → F)
    (p : E × ℝ) (m : ℕ) : Jet E F m :=
  timeGlue (iteratedFDerivWithin ℝ m f (O ×ˢ Icc 0 S)) (negativeJet O χ f m) p

theorem seeleyExtend_taylor {O W : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWO : closure W ⊆ O)
    (hδ : 0 < δ) (hδS : δ < S) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hχone : ∀ s : ℝ, |s| ≤ δ / 2 → χ s = 1)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) :
    HasFTaylorSeriesUpToOn ∞ (seeleyExtend χ f) (gluedJet O S χ f) (W ×ˢ Iio S) := by
  have hS : 0 < S := hδ.trans hδS
  have hWsub : W ⊆ O := fun x hx => hWO (subset_closure hx)
  have hpositive := (hf.ftaylorSeriesWithin
    (hO.uniqueDiffOn.prod (uniqueDiffOn_Icc hS))).mono
      (Set.prod_mono hWsub (Subset.refl _))
  have hmatch (m : ℕ) (x : E) :
      iteratedFDerivWithin ℝ m f (O ×ˢ Icc 0 S) (x, 0) =
        negativeJet O χ f m (x, 0) :=
    (negativeJet_at_zero hδ hS hχone m x).symm
  have hder (m : ℕ) (p : E × ℝ) (hp : p ∈ W ×ˢ Iio S) :
      HasFDerivAt (fun q => gluedJet O S χ f q m) (gluedJet O S χ f p (m + 1)).curryLeft p := by
    have hm : (m : ℕ∞ω) < ∞ := by
      exact_mod_cast (show (m : ℕ∞) < ⊤ by simp)
    have hd := timeGlue_hasFDerivAt hW
      (iteratedFDerivWithin ℝ m f (O ×ˢ Icc 0 S)) (negativeJet O χ f m)
      (fun q => (iteratedFDerivWithin ℝ (m + 1) f (O ×ˢ Icc 0 S) q).curryLeft)
      (fun q => (negativeJet O χ f (m + 1) q).curryLeft)
      (fun x _ => hmatch m x) (fun x _ => congrArg ContinuousMultilinearMap.curryLeft (hmatch (m + 1) x))
      (fun q hq => hpositive.fderivWithin m hm q hq)
      (fun q hq => negativeJet_hasFDerivWithinAt hO hW hWc hWO hδ hδS hχ hχzero hf m q hq) p hp
    have heq : (gluedJet O S χ f p (m + 1)).curryLeft =
        timeGlue
          (fun q => (iteratedFDerivWithin ℝ (m + 1) f (O ×ˢ Icc 0 S) q).curryLeft)
          (fun q => (negativeJet O χ f (m + 1) q).curryLeft) p := by
      dsimp only [gluedJet, timeGlue]
      split <;> rfl
    rw [heq]
    exact hd
  refine ⟨?_, fun m _ p hp => (hder m p hp).hasFDerivWithinAt,
    fun m _ p hp => (hder m p hp).continuousAt.continuousWithinAt⟩
  intro p _
  by_cases ht : p.2 < 0
  · simp only [gluedJet, timeGlue, ht, ite_true, seeleyExtend]
    exact negativeJet_zero_curry O χ f p
  · simp only [gluedJet, timeGlue, ht, ite_false, seeleyExtend,
      iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
      continuousMultilinearCurryFin0_symm_apply, ContinuousMultilinearMap.curry0_apply,
      ContinuousMultilinearMap.uncurry0_apply]

theorem seeleyExtend_contDiffOn {O W : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWO : closure W ⊆ O)
    (hδ : 0 < δ) (hδS : δ < S) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hχone : ∀ s : ℝ, |s| ≤ δ / 2 → χ s = 1)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) :
    ContDiffOn ℝ ∞ (seeleyExtend χ f) (W ×ˢ Iio S) :=
  (seeleyExtend_taylor hO hW hWc hWO hδ hδS hχ hχzero hχone hf).contDiffOn

end Yau.F04Proof.Seeley
