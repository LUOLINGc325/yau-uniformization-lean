import Yau.LeafProofs.L17UniformJets

/-! Uniform jet bounds under bilinear operations and smooth composition. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux.UniformJetBounds

variable {ι κ E F G H : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {k : ℕ}

theorem reindex {f : ι → E → F} {s : ι → Set E}
    (h : UniformJetBounds k f s) (r : κ → ι) :
    UniformJetBounds k (fun a => f (r a)) (fun a => s (r a)) := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun a x hx j hj => hb (r a) x hx j hj⟩

theorem bilinear {f : ι → E → F} {g : ι → E → G} {s : ι → Set E}
    (hf : UniformJetBounds k f s) (hg : UniformJetBounds k g s)
    (hs : ∀ i, IsOpen (s i))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (s i))
    (hgs : ∀ i, ContDiffOn ℝ ∞ (g i) (s i)) (B : F →L[ℝ] G →L[ℝ] H) :
    UniformJetBounds k (fun i x => B (f i x) (g i x)) s := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨D, hD, hd⟩ := hg
  apply of_orderBounds
  intro m hm
  refine ⟨‖B‖ * ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * C * D, ?_⟩
  intro i x hx
  have hnorm := B.norm_iteratedFDerivWithin_le_of_bilinear (hfs i) (hgs i)
    (hs i).uniqueDiffOn hx (by simp : (m : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ (hs i) hx] at hnorm
  apply hnorm.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  apply mul_le_mul
    (mul_le_mul_of_nonneg_left (hb i x hx j (hjm.trans hm)) (Nat.cast_nonneg _))
    (hd i x hx (m - j) ((Nat.sub_le _ _).trans hm))
    (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hC))

theorem comp {f : ι → E → F} {g : ι → F → G}
    {s : ι → Set E} {t : ι → Set F}
    (hf : UniformJetBounds k f s) (hg : UniformJetBounds k g t)
    (hs : ∀ i, IsOpen (s i)) (ht : ∀ i, IsOpen (t i))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (s i))
    (hgs : ∀ i, ContDiffOn ℝ ∞ (g i) (t i)) (hmap : ∀ i, MapsTo (f i) (s i) (t i)) :
    UniformJetBounds k (fun i x => g i (f i x)) s := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨D, hD, hd⟩ := hg
  apply of_orderBounds
  intro m hm
  refine ⟨(m.factorial : ℝ) * D * C ^ m, ?_⟩
  intro i x hx
  have houter (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j (g i) (t i) (f i x)‖ ≤ D := by
    rw [iteratedFDerivWithin_of_isOpen j (ht i) (hmap i hx)]
    exact hd i (f i x) (hmap i hx) j (hj.trans hm)
  have hinner (j : ℕ) (hjpos : 1 ≤ j) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j (f i) (s i) x‖ ≤ C ^ j := by
    rw [iteratedFDerivWithin_of_isOpen j (hs i) hx]
    exact (hb i x hx j (hj.trans hm)).trans (le_self_pow₀ hC (by omega))
  have hnorm := norm_iteratedFDerivWithin_comp_le (hgs i) (hfs i)
    (by simp : (m : ℕ∞ω) ≤ ∞) (ht i).uniqueDiffOn (hs i).uniqueDiffOn
    (hmap i) hx houter hinner
  rw [iteratedFDerivWithin_of_isOpen m (hs i) hx] at hnorm
  exact hnorm

theorem constant {s : ι → Set E} (c : F) :
    UniformJetBounds k (fun _ _ => c) s := by
  refine ⟨max 1 ‖c‖, le_max_left _ _, ?_⟩
  intro i x hx j hj
  cases j with
  | zero => exact (norm_iteratedFDeriv_zero.trans_le (le_max_right _ _))
  | succ j =>
    rw [← iteratedFDerivWithin_univ, iteratedFDerivWithin_succ_const]
    simp only [Pi.zero_apply, norm_zero]
    exact zero_le_one.trans (le_max_left _ _)

end Yau.LeafProofs.L17Aux.UniformJetBounds
