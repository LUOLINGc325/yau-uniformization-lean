import Yau.Proofs.F04SeeleyBoundaryJets

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def negativeJetTerm (O : Set E) (χ : ℝ → ℝ) (f : E × ℝ → F)
    (m k : ℕ) (p : E × ℝ) : Jet E F m :=
  seeleyWeight k •
    (iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0) (reflectLinear k p)).compContinuousLinearMap
      (fun _ : Fin m => reflectLinear k)

theorem negativeJetTerm_norm_le (O : Set E) (χ : ℝ → ℝ) (f : E × ℝ → F)
    (m k : ℕ) (p : E × ℝ) (M : ℝ)
    (hJ : ‖iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0) (reflectLinear k p)‖ ≤ M) :
    ‖negativeJetTerm O χ f m k p‖ ≤ (|seeleyWeight k| * dyadic k ^ m) * M := by
  rw [negativeJetTerm, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |seeleyWeight k| *
        (‖iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0) (reflectLinear k p)‖ * dyadic k ^ m) :=
      mul_le_mul_of_nonneg_left (tensor_pullback_norm_le m k _) (abs_nonneg _)
    _ ≤ |seeleyWeight k| * (M * dyadic k ^ m) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hJ (pow_nonneg (dyadic_pos k).le _))
        (abs_nonneg _)
    _ = _ := by ring

variable [CompleteSpace F]

theorem negativeJet_continuousOn {O W : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (_hW : IsOpen W) (hWc : IsCompact (closure W)) (hWO : closure W ⊆ O)
    (hδ : 0 < δ) (hδS : δ < S) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) (m : ℕ) :
    ContinuousOn (negativeJet O χ f m) (W ×ˢ Iic 0) := by
  have hg := positiveCutoff_contDiffOn hO hδ hδS hχ hχzero hf
  have hu : UniqueDiffOn ℝ (O ×ˢ Ici (0 : ℝ)) := hO.uniqueDiffOn.prod (uniqueDiffOn_Ici 0)
  have hJ : ContinuousOn
      (iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0)) (O ×ˢ Ici 0) :=
    (hg.ftaylorSeriesWithin hu).cont m (by simp)
  have hmaps (k : ℕ) : MapsTo (reflectLinear (E := E) k) (W ×ˢ Iic 0) (O ×ˢ Ici 0) := by
    intro p hp
    rw [reflectLinear_apply]
    exact ⟨hWO (subset_closure hp.1),
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (dyadic_pos k).le) hp.2⟩
  have hterm (k : ℕ) : ContinuousOn (negativeJetTerm O χ f m k) (W ×ˢ Iic 0) := by
    have hcomp := hJ.comp (reflectLinear k).continuous.continuousOn (hmaps k)
    have hpull := (ContinuousMultilinearMap.continuous_precomp
      (fun _ : Fin m => reflectLinear (E := E) k)).comp_continuousOn hcomp
    exact (continuousOn_const (c := seeleyWeight k)).smul hpull
  obtain ⟨M, _hM, hM⟩ := positiveCutoff_jet_bound hO hWc hWO hδ hδS hχ hχzero hf m
  have hbound (k : ℕ) (p : E × ℝ) (hp : p ∈ W ×ˢ Iic 0) :
      ‖negativeJetTerm O χ f m k p‖ ≤ (|seeleyWeight k| * dyadic k ^ m) * M := by
    apply negativeJetTerm_norm_le
    have ht : 0 ≤ -dyadic k * p.2 :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (dyadic_pos k).le) hp.2
    have he := hM p.1 (subset_closure hp.1) (-dyadic k * p.2) ht
    simpa only [reflectLinear_apply] using he
  exact continuousOn_tsum hterm ((seeleyWeight_summable m).mul_right M) hbound

end Yau.F04Proof.Seeley
