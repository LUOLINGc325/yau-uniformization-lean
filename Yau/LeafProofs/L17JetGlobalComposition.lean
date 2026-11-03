import Yau.LeafProofs.L17ConnectionJets

/-! Finite products and globally smooth finite-dimensional operations preserve uniform jets. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux.UniformJetBounds

variable {ι E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {k : ℕ} {s : ι → Set E}

theorem prodMk {f : ι → E → F} {g : ι → E → G}
    (hf : UniformJetBounds k f s) (hg : UniformJetBounds k g s)
    (hs : ∀ i, IsOpen (s i))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (s i))
    (hgs : ∀ i, ContDiffOn ℝ ∞ (g i) (s i)) :
    UniformJetBounds k (fun i x => (f i x, g i x)) s := by
  let L := ContinuousLinearMap.inl ℝ F G
  let R := ContinuousLinearMap.inr ℝ F G
  have hl := hf.comp_clm hs hfs L
  have hr := hg.comp_clm hs hgs R
  have hls (i : ι) := L.contDiff.comp_contDiffOn (hfs i)
  have hrs (i : ι) := R.contDiff.comp_contDiffOn (hgs i)
  apply (hl.add hr hs hls hrs).congr hs
  intro i x hx
  simp [L, R]

theorem comp_global [FiniteDimensional ℝ F] {f : ι → E → F}
    (hf : UniformJetBounds k f s) (hs : ∀ i, IsOpen (s i))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (s i))
    {g : F → G} (hg : ContDiff ℝ ∞ g) :
    UniformJetBounds k (fun i x => g (f i x)) s := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨V, hVo, hKV, _, hVjets⟩ := compact_buffer_uniformJetBounds (ι := ι)
    (isCompact_closedBall (0 : F) C) isOpen_univ (subset_univ _) hg.contDiffOn
  have hmap (i : ι) : MapsTo (f i) (s i) V := by
    intro x hx
    apply hKV
    apply mem_closedBall.mpr
    simpa only [dist_zero_right, norm_iteratedFDeriv_zero] using hb i x hx 0 (Nat.zero_le _)
  exact (show UniformJetBounds k f s from ⟨C, hC, hb⟩).comp (hVjets k)
    hs (fun _ => hVo) hfs (fun _ => hg.contDiffOn) hmap

end Yau.LeafProofs.L17Aux.UniformJetBounds
