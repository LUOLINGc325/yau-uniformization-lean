import Yau.LeafProofs.L17TransitionConnection

/-! Uniform bounds on actual finite jets, with elementary closure rules. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L17Aux

variable {ι E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

def UniformJetBounds (k : ℕ) (f : ι → E → F) (s : ι → Set E) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ i x, x ∈ s i → ∀ j, j ≤ k →
    ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C

namespace UniformJetBounds

variable {k l : ℕ} {f g : ι → E → F} {s t : ι → Set E}

theorem mono_order (h : UniformJetBounds k f s) (hl : l ≤ k) :
    UniformJetBounds l f s := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun i x hx j hj => hb i x hx j (hj.trans hl)⟩

theorem mono_sets (h : UniformJetBounds k f s) (ht : ∀ i, t i ⊆ s i) :
    UniformJetBounds k f t := by
  obtain ⟨C, hC, hb⟩ := h
  exact ⟨C, hC, fun i x hx j hj => hb i x (ht i hx) j hj⟩

theorem of_orderBounds
    (h : ∀ j, j ≤ k → ∃ C : ℝ, ∀ i x, x ∈ s i →
      ‖iteratedFDeriv ℝ j (f i) x‖ ≤ C) : UniformJetBounds k f s := by
  classical
  have hj (j : Fin (k + 1)) : ∃ C : ℝ, 1 ≤ C ∧ ∀ i x, x ∈ s i →
      ‖iteratedFDeriv ℝ j.val (f i) x‖ ≤ C := by
    obtain ⟨C, hC⟩ := h j.val (Nat.le_of_lt_succ j.isLt)
    exact ⟨max 1 C, le_max_left _ _, fun i x hx => (hC i x hx).trans (le_max_right _ _)⟩
  choose C hC hb using hj
  have hn : ∀ j, 0 ≤ C j := fun j => zero_le_one.trans (hC j)
  refine ⟨1 + ∑ j, C j, le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hn j), ?_⟩
  intro i x hx j hjk
  let a : Fin (k + 1) := ⟨j, Nat.lt_succ_of_le hjk⟩
  have hcj : C a ≤ ∑ b, C b := Finset.single_le_sum (fun b _ => hn b) (Finset.mem_univ a)
  exact (hb a i x hx).trans (hcj.trans (by linarith))

theorem congr (h : UniformJetBounds k f s) (hs : ∀ i, IsOpen (s i))
    (heq : ∀ i, EqOn (f i) (g i) (s i)) : UniformJetBounds k g s := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_⟩
  intro i x hx j hj
  have hsame := iteratedFDerivWithin_congr (𝕜 := ℝ) (heq i) hx j
  rw [iteratedFDerivWithin_of_isOpen j (hs i) hx,
    iteratedFDerivWithin_of_isOpen j (hs i) hx] at hsame
  rw [← hsame]
  exact hb i x hx j hj

theorem fderiv (h : UniformJetBounds (k + 1) f s) :
    UniformJetBounds k (fun i => _root_.fderiv ℝ (f i)) s := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, ?_⟩
  intro i x hx j hj
  rw [norm_iteratedFDeriv_fderiv]
  exact hb i x hx (j + 1) (Nat.add_le_add_right hj 1)

theorem comp_clm (h : UniformJetBounds k f s)
    (hs : ∀ i, IsOpen (s i)) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (s i))
    (L : F →L[ℝ] G) : UniformJetBounds k (fun i x => L (f i x)) s := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨1 + ‖L‖ * C,
    le_add_of_nonneg_right (mul_nonneg (norm_nonneg L) (zero_le_one.trans hC)), ?_⟩
  intro i x hx j hj
  have hd := (hf i).contDiffAt ((hs i).mem_nhds hx)
  have hnorm := L.norm_iteratedFDeriv_comp_left hd (by simp : (j : ℕ∞ω) ≤ ∞)
  exact hnorm.trans ((mul_le_mul_of_nonneg_left (hb i x hx j hj) (norm_nonneg L)).trans
    (by linarith))

theorem add (hf : UniformJetBounds k f s) (hg : UniformJetBounds k g s)
    (hs : ∀ i, IsOpen (s i))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (s i))
    (hgs : ∀ i, ContDiffOn ℝ ∞ (g i) (s i)) :
    UniformJetBounds k (fun i x => f i x + g i x) s := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨D, hD, hd⟩ := hg
  refine ⟨C + D, by linarith, ?_⟩
  intro i x hx j hj
  have hfj := ((hfs i).contDiffAt ((hs i).mem_nhds hx)).of_le (by simp : (j : ℕ∞ω) ≤ ∞)
  have hgj := ((hgs i).contDiffAt ((hs i).mem_nhds hx)).of_le (by simp : (j : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ j (f i + g i) x‖ ≤ C + D
  rw [iteratedFDeriv_add_apply hfj hgj]
  exact (norm_add_le _ _).trans (add_le_add (hb i x hx j hj) (hd i x hx j hj))

theorem sub (hf : UniformJetBounds k f s) (hg : UniformJetBounds k g s)
    (hs : ∀ i, IsOpen (s i))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (s i))
    (hgs : ∀ i, ContDiffOn ℝ ∞ (g i) (s i)) :
    UniformJetBounds k (fun i x => f i x - g i x) s := by
  obtain ⟨C, hC, hb⟩ := hf
  obtain ⟨D, hD, hd⟩ := hg
  refine ⟨C + D, by linarith, ?_⟩
  intro i x hx j hj
  have hfj := ((hfs i).contDiffAt ((hs i).mem_nhds hx)).of_le (by simp : (j : ℕ∞ω) ≤ ∞)
  have hgj := ((hgs i).contDiffAt ((hs i).mem_nhds hx)).of_le (by simp : (j : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ j (f i - g i) x‖ ≤ C + D
  rw [iteratedFDeriv_sub_apply hfj hgj]
  exact (norm_sub_le _ _).trans (add_le_add (hb i x hx j hj) (hd i x hx j hj))

theorem finite_sum {κ : Type*} [Fintype κ]
    {v : κ → ι → E → F} (hv : ∀ a, UniformJetBounds k (v a) s)
    (hs : ∀ i, IsOpen (s i))
    (hvs : ∀ a i, ContDiffOn ℝ ∞ (v a i) (s i)) :
    UniformJetBounds k (fun i x => ∑ a, v a i x) s := by
  classical
  choose C hC hb using hv
  have hn : ∀ a, 0 ≤ C a := fun a => zero_le_one.trans (hC a)
  refine ⟨1 + ∑ a, C a, le_add_of_nonneg_right (Finset.sum_nonneg fun a _ => hn a), ?_⟩
  intro i x hx j hj
  have hsmooth (a : κ) (_ : a ∈ Finset.univ) : ContDiffAt ℝ j (v a i) x :=
    ((hvs a i).contDiffAt ((hs i).mem_nhds hx)).of_le (by simp)
  rw [iteratedFDeriv_fun_sum_apply hsmooth]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun a _ => hb a i x hx j hj).trans
    (by linarith))

theorem pi {κ : Type*} [Fintype κ]
    {v : κ → ι → E → F} (hv : ∀ a, UniformJetBounds k (v a) s)
    (hs : ∀ i, IsOpen (s i))
    (hvs : ∀ a i, ContDiffOn ℝ ∞ (v a i) (s i)) :
    UniformJetBounds k (fun i x a => v a i x) s := by
  classical
  let L (a : κ) : F →L[ℝ] (κ → F) := ContinuousLinearMap.single ℝ (fun _ : κ => F) a
  have hb (a : κ) := (hv a).comp_clm hs (hvs a) (L a)
  have hbs (a : κ) (i : ι) : ContDiffOn ℝ ∞ (fun x => L a (v a i x)) (s i) :=
    (L a).contDiff.comp_contDiffOn (hvs a i)
  apply (finite_sum hb hs hbs).congr hs
  intro i x hx
  ext a
  simp [L]

end UniformJetBounds

end Yau.LeafProofs.L17Aux
