import Yau.Proofs.D04Anchors

open Filter Set

noncomputable section

namespace Yau.Proofs.D04Aux

/-- A nested extraction has one diagonal whose every tail is a genuine
strictly increasing subsequence of the corresponding stage. -/
theorem nested_subsequence_diagonal
    (s r : ℕ → ℕ → ℕ) (hs : ∀ m, StrictMono (s m)) (hr : ∀ m, StrictMono (r m))
    (hrec : ∀ m k, s (m + 1) k = s m (r m k)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∀ k, φ (k + i) = s (i + 1) (τ k) := by
  classical
  let φ : ℕ → ℕ := fun k => s (k + 1) k
  have hφ : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    change s (k + 1) k < s ((k + 1) + 1) (k + 1)
    rw [hrec (k + 1) (k + 1)]
    exact hs (k + 1) ((Nat.lt_succ_self k).trans_le ((hr (k + 1)).id_le (k + 1)))
  have hanti : Antitone (fun m => range (s m)) := by
    apply antitone_nat_of_succ_le
    intro m y hy
    obtain ⟨k, rfl⟩ := hy
    exact ⟨r m k, (hrec m k).symm⟩
  refine ⟨φ, hφ, ?_⟩
  intro i
  have hmem (k : ℕ) : ∃ j, s (i + 1) j = φ (k + i) := by
    apply hanti (show i + 1 ≤ k + i + 1 by omega)
    exact mem_range_self (k + i)
  choose τ hτ using hmem
  refine ⟨τ, ?_, fun k => (hτ k).symm⟩
  intro a b hab
  apply (hs (i + 1)).lt_iff_lt.mp
  rw [hτ a, hτ b]
  exact hφ (Nat.add_lt_add_right hab i)

/-- Convergence of an actual stage subsequence transfers through the exact
tail factorization; finite prefixes disappear by the atTop shift theorem. -/
theorem tendsto_of_subsequence_tail
    {α : Type*} {l : Filter α} (f : ℕ → α) {φ s τ : ℕ → ℕ} {i : ℕ}
    (hτ : StrictMono τ) (hfactor : ∀ k, φ (k + i) = s (τ k))
    (ht : Tendsto (fun j => f (s j)) atTop l) :
    Tendsto (fun j => f (φ j)) atTop l := by
  have htail : Tendsto (fun k => f (φ (k + i))) atTop l := by
    simpa only [hfactor, Function.comp_def] using ht.comp hτ.tendsto_atTop
  exact (tendsto_add_atTop_iff_nat i).mp htail

theorem eventually_of_subsequence_tail
    {P : ℕ → Prop} {φ s τ : ℕ → ℕ} {i : ℕ}
    (hτ : StrictMono τ) (hfactor : ∀ k, φ (k + i) = s (τ k))
    (h : ∀ᶠ j in atTop, P (s j)) : ∀ᶠ j in atTop, P (φ j) := by
  have htail : ∀ᶠ k in atTop, P (φ (k + i)) := by
    simpa only [hfactor, Function.comp_def] using hτ.tendsto_atTop.eventually h
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  refine eventually_atTop.mpr ⟨N + i, ?_⟩
  intro j hj
  have hk : N ≤ j - i := by omega
  have heq : j - i + i = j := by omega
  simpa only [heq] using hN (j - i) hk

end Yau.Proofs.D04Aux
