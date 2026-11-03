import Yau.Proofs.F04SeeleyNegativeContinuity

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem negativeTerm_taylor {O : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (hδ : 0 < δ) (hδS : δ < S) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) (k : ℕ) :
    HasFTaylorSeriesUpToOn ∞
      (fun p => seeleyWeight k • positiveCutoff χ f (reflectLinear k p))
      (fun p m => negativeJetTerm O χ f m k p) (O ×ˢ Iic 0) := by
  have hg := positiveCutoff_contDiffOn hO hδ hδS hχ hχzero hf
  have hu : UniqueDiffOn ℝ (O ×ˢ Ici (0 : ℝ)) := hO.uniqueDiffOn.prod (uniqueDiffOn_Ici 0)
  have ht := (hg.ftaylorSeriesWithin hu).compContinuousLinearMap (reflectLinear k)
  have htw := HasFTaylorSeriesUpToOn.continuousLinearMap_comp
    ((seeleyWeight k) • ContinuousLinearMap.id ℝ F) ht
  have hcoeff : HasFTaylorSeriesUpToOn ∞
      (fun p => seeleyWeight k • positiveCutoff χ f (reflectLinear k p))
      (fun p m => negativeJetTerm O χ f m k p)
      ((reflectLinear k) ⁻¹' (O ×ˢ Ici 0)) := by
    apply htw.congr_series
    intro m _ p _
    ext v
    rfl
  apply hcoeff.mono
  intro p hp
  rw [mem_preimage, reflectLinear_apply]
  exact ⟨hp.1, mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (dyadic_pos k).le) hp.2⟩

theorem negativeJetTerm_hasFDerivAt {O : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (hδ : 0 < δ) (hδS : δ < S) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) (m k : ℕ) (p : E × ℝ)
    (hp : p ∈ O ×ˢ Iio 0) :
    HasFDerivAt (negativeJetTerm O χ f m k)
      (negativeJetTerm O χ f (m + 1) k p).curryLeft p := by
  have ht := (negativeTerm_taylor hO hδ hδS hχ hχzero hf k).mono
    (show O ×ˢ Iio (0 : ℝ) ⊆ O ×ˢ Iic 0 from
      fun p hq => ⟨hq.1, (show p.2 < (0 : ℝ) from hq.2).le⟩)
  have hm : (m : ℕ∞ω) < ∞ := by
    exact_mod_cast (show (m : ℕ∞) < ⊤ by simp)
  exact (ht.fderivWithin m hm p hp).hasFDerivAt ((hO.prod isOpen_Iio).mem_nhds hp)

end Yau.F04Proof.Seeley
