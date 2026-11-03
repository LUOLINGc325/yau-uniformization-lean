import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactness.Compact

open scoped Topology unitInterval

noncomputable section

namespace Yau.Proofs.C07PolygonalPrefixAux

open Set

theorem exists_partition_piece {m : ℕ} (hm : 0 < m) (t : ℕ → I)
    (ht0 : t 0 = 0) (htm : t m = 1) (u : I) :
    ∃ i : Fin m, u ∈ Icc (t i) (t (i + 1)) := by
  cases m with
  | zero => exact (Nat.not_lt_zero _ hm).elim
  | succ m =>
    have hex : ∃ j : ℕ, u ≤ t (j + 1) := ⟨m, by rw [htm]; exact u.2.2⟩
    have hj : Nat.find hex ≤ m := Nat.find_min' hex (by rw [htm]; exact u.2.2)
    refine ⟨⟨Nat.find hex, Nat.lt_succ_of_le hj⟩, ?_, Nat.find_spec hex⟩
    change t (Nat.find hex) ≤ u
    cases hf : Nat.find hex with
    | zero =>
      rw [ht0]
      exact u.2.1
    | succ k =>
      have hk : k < Nat.find hex := by omega
      have hnot := Nat.find_min hex hk
      exact le_of_lt (lt_of_not_ge (by simpa only [hf, Nat.succ_eq_add_one] using hnot))

/-- A finite partition adapted to one row of a continuous square remains
adapted on a common open neighborhood of that row. -/
theorem exists_local_partition {X : Type*} [TopologicalSpace X] {ι : Type*}
    (H : C(I × I, X)) (c : ι → Set X) (hc : ∀ i, IsOpen (c i))
    (hcover : (⋃ i, c i) = univ) (s₀ : I) :
    ∃ (m : ℕ) (t : ℕ → I) (b : Fin m → ι) (N : Set I),
      0 < m ∧ t 0 = 0 ∧ t m = 1 ∧ Monotone t ∧ IsOpen N ∧ s₀ ∈ N ∧
      ∀ (i : Fin m) (s : I), s ∈ N →
        ∀ u ∈ Icc (t i) (t (i + 1)), H (u, s) ∈ c (b i) := by
  classical
  let d : ι → Set I := fun i => (fun u => H (u, s₀)) ⁻¹' c i
  have hd : ∀ i, IsOpen (d i) := fun i =>
    (hc i).preimage (H.continuous.comp (continuous_id.prodMk continuous_const))
  have hdcover : univ ⊆ ⋃ i, d i := by
    intro u _
    have hu : H (u, s₀) ∈ ⋃ i, c i := by rw [hcover]; trivial
    simpa only [mem_iUnion, d, mem_preimage] using hu
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, hpiece⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hd hdcover
  let q := m + 1
  choose b hb using fun i : Fin q => hpiece i
  have htube : ∀ i : Fin q, ∃ N : Set I,
      IsOpen N ∧ s₀ ∈ N ∧
        ∀ s ∈ N, ∀ u ∈ Icc (t i) (t (i + 1)), H (u, s) ∈ c (b i) := by
    intro i
    have hopen : IsOpen (H ⁻¹' c (b i)) := (hc _).preimage H.continuous
    have hsub : Icc (t i) (t (i + 1)) ×ˢ {s₀} ⊆ H ⁻¹' c (b i) := by
      rintro ⟨u, s⟩ ⟨hu, hs⟩
      have hs' : s = s₀ := mem_singleton_iff.mp hs
      subst s
      exact hb i hu
    obtain ⟨U, N, _, hN, hUsub, hsN, hUN⟩ :=
      generalized_tube_lemma isCompact_Icc isCompact_singleton hopen hsub
    exact ⟨N, hN, hsN (mem_singleton s₀), fun s hs u hu => hUN ⟨hUsub hu, hs⟩⟩
  choose N hNopen hsN hN using htube
  refine ⟨q, t, b, ⋂ i, N i, Nat.zero_lt_succ m, ht0, hm q (Nat.le_succ m),
    hmono, isOpen_iInter_of_finite hNopen, mem_iInter.mpr hsN, ?_⟩
  intro i s hs u hu
  exact hN i s (mem_iInter.mp hs i) u hu

end Yau.Proofs.C07PolygonalPrefixAux
