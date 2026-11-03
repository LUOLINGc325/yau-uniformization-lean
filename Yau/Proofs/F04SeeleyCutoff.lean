import Yau.Proofs.F04SeeleyTensor

/-! Cutoff of only the physical nonnegative-time input and bounds on its
actual one-sided Fréchet tensors, before reflecting any value. -/

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def positiveCutoff (χ : ℝ → ℝ) (f : E × ℝ → F) : E × ℝ → F := fun p => χ p.2 • f p

omit [NormedSpace ℝ E] in
theorem positiveCutoff_zero_germ {χ : ℝ → ℝ} {δ : ℝ} {f : E × ℝ → F}
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0) (p : E × ℝ) (hp : δ < p.2) :
    positiveCutoff χ f =ᶠ[𝓝 p] fun _ => 0 := by
  have hn : {q : E × ℝ | δ < q.2} ∈ 𝓝 p :=
    continuous_snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hp)
  filter_upwards [hn] with q hq
  change χ q.2 • f q = 0
  rw [hχzero q.2 hq.le, zero_smul]

theorem positiveCutoff_contDiffOn {O : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (_hO : IsOpen O) (_hδ : 0 < δ) (hδS : δ < S) (hχ : ContDiff ℝ ∞ χ)
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) :
    ContDiffOn ℝ ∞ (positiveCutoff χ f) (O ×ˢ Ici 0) := by
  intro p hp
  by_cases ht : p.2 < S
  · have hQ : O ×ˢ Icc (0 : ℝ) S ∈ 𝓝[O ×ˢ Ici 0] p := by
      have hn : {q : E × ℝ | q.2 < S} ∈ 𝓝 p :=
        continuous_snd.continuousAt.preimage_mem_nhds (Iio_mem_nhds ht)
      apply mem_of_superset (inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hn))
      intro q hq
      exact ⟨hq.1.1, hq.1.2, hq.2.le⟩
    have hff := (hf p ⟨hp.1, hp.2, ht.le⟩).mono_of_mem_nhdsWithin hQ
    exact ((hχ.comp contDiff_snd).contDiffAt.contDiffWithinAt).smul hff
  · have hδp : δ < p.2 := hδS.trans_le (le_of_not_gt ht)
    exact ((contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      (positiveCutoff_zero_germ hχzero p hδp)).contDiffWithinAt

theorem positiveCutoff_jet_zero {χ : ℝ → ℝ} {δ : ℝ} {f : E × ℝ → F}
    (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0) (O : Set E) (m : ℕ)
    (p : E × ℝ) (hp : δ < p.2) :
    iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0) p = 0 := by
  have he := positiveCutoff_zero_germ (f := f) hχzero p hp
  rw [(he.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq he.eq_of_nhds m]
  exact congrFun (iteratedFDerivWithin_zero (𝕜 := ℝ) (E := E × ℝ) (F := F)
    (s := O ×ˢ Ici 0) (i := m)) p

theorem positiveCutoff_jet_bound {O K : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O) (hδ : 0 < δ) (hδS : δ < S)
    (hχ : ContDiff ℝ ∞ χ) (hχzero : ∀ s : ℝ, δ ≤ s → χ s = 0)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) (m : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x ∈ K, ∀ s ∈ Ici (0 : ℝ),
      ‖iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0) (x, s)‖ ≤ M := by
  have hg := positiveCutoff_contDiffOn hO hδ hδS hχ hχzero hf
  have hu : UniqueDiffOn ℝ (O ×ˢ Ici (0 : ℝ)) := hO.uniqueDiffOn.prod (uniqueDiffOn_Ici 0)
  have hc : ContinuousOn
      (iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0)) (K ×ˢ Icc 0 δ) := by
    exact ((hg.ftaylorSeriesWithin hu).cont m (by simp)).mono
      (fun p hp => ⟨hKO hp.1, hp.2.1⟩)
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨1 + |C|, by linarith [abs_nonneg C], ?_⟩
  intro x hx s hs
  by_cases hsd : s ≤ δ
  · exact (hC (x, s) ⟨hx, hs, hsd⟩).trans (by linarith [le_abs_self C])
  · rw [positiveCutoff_jet_zero hχzero O m (x, s) (lt_of_not_ge hsd), norm_zero]
    positivity

end Yau.F04Proof.Seeley
