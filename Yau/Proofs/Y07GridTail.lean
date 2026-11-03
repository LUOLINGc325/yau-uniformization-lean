import Yau.Blueprint.ModelAssembly

/-! Exact tail restriction of the canonical macro subdivision. -/

noncomputable section

namespace Yau.NodeProofs.Y07Aux

open Yau.Blueprint.Alignment

variable (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ)

/-- Splitting the finite macro count at an intermediate starting point. -/
theorem offset_add {jBase j₀ j : ℕ} (hb : jBase ≤ j₀) (hj : j₀ ≤ j) :
    offset Q N M hm jBase j =
      offset Q N M hm jBase j₀ + offset Q N M hm j₀ j := by
  unfold offset
  rw [show j - jBase = (j₀ - jBase) + (j - j₀) by omega,
    Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  omega

theorem offset_succ {jBase j : ℕ} (hj : jBase ≤ j) :
    offset Q N M hm jBase (j + 1) =
      offset Q N M hm jBase j + pieces Q N M hm j := by
  rw [offset_add Q N M hm hj (Nat.le_succ j)]
  simp [offset]

theorem offset_mono {jBase i j : ℕ} (hi : jBase ≤ i) (hij : i ≤ j) :
    offset Q N M hm jBase i ≤ offset Q N M hm jBase j := by
  rw [offset_add Q N M hm hi hij]
  omega

/-- The same subdivision interval contains the shifted global index. -/
theorem macroAt_tail {jBase j₀ : ℕ} (hb : jBase ≤ j₀)
    (hlayout : GridLayout Q N M hm j₀) (k : ℕ) :
    macroAt Q N M hm jBase (offset Q N M hm jBase j₀ + k) =
      macroAt Q N M hm j₀ k := by
  let j := macroAt Q N M hm j₀ k
  obtain ⟨hj, hslot, hdecomp⟩ := hlayout.2.2.2.1 k
  have hbj : jBase ≤ j := hb.trans hj
  have hsplit := offset_add Q N M hm hb hj
  have hindex : offset Q N M hm jBase j₀ + k =
      offset Q N M hm jBase j + slotAt Q N M hm j₀ k := by
    dsimp only [j] at *
    omega
  have hmem : j ∈ {r | jBase ≤ r ∧ offset Q N M hm jBase j₀ + k <
      offset Q N M hm jBase (r + 1)} := by
    refine ⟨hbj, ?_⟩
    rw [offset_succ Q N M hm hbj]
    dsimp only [j] at *
    omega
  change sInf {r | jBase ≤ r ∧ offset Q N M hm jBase j₀ + k <
    offset Q N M hm jBase (r + 1)} = j
  apply IsLeast.csInf_eq
  refine ⟨hmem, ?_⟩
  rintro r ⟨hrbase, hrend⟩
  by_contra hn
  have hrj : r + 1 ≤ j := by omega
  have hle := offset_mono Q N M hm (show jBase ≤ r + 1 by omega) hrj
  dsimp only [j] at *
  omega

/-- The local slot is preserved by the canonical shift. -/
theorem slotAt_tail {jBase j₀ : ℕ} (hb : jBase ≤ j₀)
    (hlayout : GridLayout Q N M hm j₀) (k : ℕ) :
    slotAt Q N M hm jBase (offset Q N M hm jBase j₀ + k) =
      slotAt Q N M hm j₀ k := by
  have hj := (hlayout.2.2.2.1 k).1
  have hsplit := offset_add Q N M hm hb hj
  unfold slotAt
  rw [macroAt_tail Q N M hm hb hlayout k, hsplit]
  omega

/-- Tail restriction only needs the later layout's indexing equations. -/
theorem gridClock_tail {jBase j₀ : ℕ} (hb : jBase ≤ j₀)
    (hlayout : GridLayout Q N M hm j₀) (k : ℕ) :
    gridClock Q N M hm j₀ k =
      gridClock Q N M hm jBase (offset Q N M hm jBase j₀ + k) := by
  simp only [gridClock, macroAt_tail Q N M hm hb hlayout k,
    slotAt_tail Q N M hm hb hlayout k]

theorem canonicalGridTail : CanonicalGridTail := by
  intro Q N M hm jBase j₀ hb _ hlate k
  exact gridClock_tail Q N M hm hb hlate k

end Yau.NodeProofs.Y07Aux
