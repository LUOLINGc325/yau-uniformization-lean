import Yau.Proofs.F01FiniteTaylorHolder

/-! All finite spatial jets of a smooth compact-range composition have
actual Holder budgets. The constants are fixed before the field and its
chart realization, and the conclusion is the native iterated derivative. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F G : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem compact_iterated_jet_holder_composition_budget
    {K U : Set F} {φ : F → G} {C : ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ ∞ φ U) (hC : 0 ≤ C) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (S : Set (Space n)) (β : ℝ)
      (f : Point n → F), IsOpen S → Q ⊆ S ×ˢ (Set.univ : Set ℝ) →
      MapsTo f Q K → HolderBound β Q f C →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => f (z, p.2)) S) →
      (∀ j : Fin (k + 1),
        HolderBound β Q (fun p => iteratedFDeriv ℝ j.val (fun z => f (z, p.2)) p.1) C) →
      HolderBound β Q (fun p => iteratedFDeriv ℝ k (fun z => φ (f (z, p.2))) p.1) B := by
  have hEach : ∀ j : Fin (k + 1), ∃ D : ℝ, 0 < D ∧
      ∀ (Q : Set (Point n)) (β : ℝ) (f : Point n → F),
      HolderBound β Q f C → MapsTo f Q K →
      HolderBound β Q (fun p => iteratedFDeriv ℝ j.val φ (f p)) D := by
    intro j
    have hφj : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ j.val φ) U := by
      apply hU.contDiffOn_iff.mpr
      intro y hy
      exact (hφ.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (by simp)
    exact compact_smooth_holder_composition_budget hU hK hConv hKU hφj hC
  choose D hD hd using hEach
  let Dall : ℝ := 1 + ∑ j, D j
  have hDall : 0 < Dall := by
    dsimp only [Dall]
    have hs : 0 ≤ ∑ j, D j := Finset.sum_nonneg (fun j _ => (hD j).le)
    linarith
  have hDj (j : Fin (k + 1)) : D j ≤ Dall := by
    have hh := Finset.single_le_sum (s := Finset.univ) (fun i _ => (hD i).le)
      (Finset.mem_univ j)
    dsimp only [Dall]
    linarith
  obtain ⟨B, hB, hb⟩ := finiteTaylorComposition_holder_budget
    (n := n) (E := Space n) (F := F) (G := G) k hDall.le hC
  refine ⟨B, hB, ?_⟩
  intro Q S β f hS hQS hmap hf hfs hj
  have hOuter : ∀ j : Fin (k + 1),
      HolderBound β Q (fun p => iteratedFDeriv ℝ j.val φ (f p)) Dall := by
    intro j
    exact holderBound_mono_const (hd j Q β f hf hmap) (hDj j)
  have hComposed := hb Q β (fun p j => iteratedFDeriv ℝ j.val φ (f p))
    (fun p j => iteratedFDeriv ℝ j.val (fun z => f (z, p.2)) p.1) hOuter hj
  have he : ∀ p ∈ Q,
      finiteTaylorComposition k
        ((fun j : Fin (k + 1) => iteratedFDeriv ℝ j.val φ (f p)),
          (fun j : Fin (k + 1) => iteratedFDeriv ℝ j.val (fun z => f (z, p.2)) p.1)) =
        iteratedFDeriv ℝ k (fun z => φ (f (z, p.2))) p.1 := by
    intro p hp
    exact finiteTaylorComposition_native
      ((hfs p hp).contDiffAt (hS.mem_nhds (hQS hp).1))
      (hφ.contDiffAt (hU.mem_nhds (hKU (hmap hp)))) k
  refine ⟨hComposed.1, ?_, ?_⟩
  · intro p hp
    change ‖iteratedFDeriv ℝ k (fun z => φ (f (z, p.2))) p.1‖ ≤ B
    rw [← he p hp]
    exact hComposed.2.1 p hp
  · intro p hp q hq
    change ‖iteratedFDeriv ℝ k (fun z => φ (f (z, p.2))) p.1 -
      iteratedFDeriv ℝ k (fun z => φ (f (z, q.2))) q.1‖ ≤ _
    rw [← he p hp, ← he q hq]
    exact hComposed.2.2 p hp q hq

end Yau.NodeProofs.F01Aux
