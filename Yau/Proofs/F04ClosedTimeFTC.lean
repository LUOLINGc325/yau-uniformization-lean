import Yau.Proofs.F04FiniteMass

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

/-- Interior derivatives and the original closed-time continuity suffice for
every oriented endpoint pair; no continuation beyond the physical slab. -/
theorem closed_time_FTC
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} {f g : ℝ → E} (hf : ContinuousOn f (Icc 0 T))
    (hg : IntegrableOn g (Icc 0 T))
    (hd : ∀ q ∈ Ioo 0 T, HasDerivAt f (g q) q)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    (∫ q in s..t, g q) = f t - f s := by
  have hle {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
      (∫ q in a..b, g q) = f b - f a := by
    have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha.1 hb.2
    have hi : IntegrableOn g (uIcc a b) := by
      simpa only [uIcc_of_le hab] using hg.mono_set hsub
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hf.mono hsub)
      (fun q hq => hd q ⟨ha.1.trans_lt hq.1, hq.2.trans_le hb.2⟩)
      hi.intervalIntegrable
  rcases le_total s t with hst | hts
  · exact hle hs ht hst
  · rw [intervalIntegral.integral_symm, hle ht hs hts, neg_sub]

end Yau.F04Proof
