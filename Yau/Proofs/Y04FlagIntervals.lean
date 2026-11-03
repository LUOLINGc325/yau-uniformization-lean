import Yau.Blueprint.Alignment

/-! Finite interval arithmetic for the literal logarithmic flag test. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y04Proof

def flagStart (Q : ℕ → ℝ) (N : ℕ) (M : ℝ) (a : ℕ) : Prop :=
  M < Real.log (Q (a + N + 1)) - Real.log (Q a)

theorem bad_iff_flagStart {Q : ℕ → ℝ} {N j : ℕ} {M : ℝ} :
    Bad Q N M j ↔
      ∃ a, flagStart Q N M a ∧ a ≤ j ∧ j < a + (2 * N + 1) := by
  constructor
  · rintro ⟨f, ⟨hNf, hf⟩, hlo, hhi⟩
    refine ⟨f - N, ?_, hlo, ?_⟩
    · simpa [flagStart, Nat.sub_add_cancel hNf] using hf
    · omega
  · rintro ⟨a, ha, hlo, hhi⟩
    refine ⟨a + N, ⟨by omega, ?_⟩, ?_, ?_⟩
    · simpa [flagStart] using ha
    · omega
    · omega

theorem flagStart_left_of_boundary
    {Q : ℕ → ℝ} {N u x a : ℕ} {M : ℝ}
    (hleft : u = 0 ∨ Regular Q N M (u - 1))
    (hux : u ≤ x) (ha : flagStart Q N M a)
    (hax : a ≤ x) (hx : x < a + (2 * N + 1)) : u ≤ a := by
  rcases hleft with rfl | hleft
  · omega
  · by_contra hn
    apply hleft
    exact bad_iff_flagStart.mpr ⟨a, ha, by omega, by omega⟩

theorem flagStart_inside_full
    {Q : ℕ → ℝ} {N u v x a : ℕ} {M : ℝ}
    (hc : FullBadComponent Q N M u v)
    (hux : u ≤ x) (hxv : x < v) (ha : flagStart Q N M a)
    (hax : a ≤ x) (hxa : x < a + (2 * N + 1)) :
    u ≤ a ∧ a + (2 * N + 1) ≤ v := by
  refine ⟨flagStart_left_of_boundary hc.2.1 hux ha hax hxa, ?_⟩
  by_contra hn
  apply hc.2.2.1
  exact bad_iff_flagStart.mpr ⟨a, ha, by omega, by omega⟩

theorem fullBadComponent_length
    {Q : ℕ → ℝ} {N u v : ℕ} {M : ℝ}
    (hc : FullBadComponent Q N M u v) : 2 * N + 1 ≤ v - u := by
  obtain ⟨a, ha, hau, hua⟩ := bad_iff_flagStart.mp (hc.2.2.2 u le_rfl hc.1)
  have h := flagStart_inside_full hc le_rfl hc.1 ha hau hua
  omega

theorem select_disjoint_equal_intervals
    (A : Finset ℕ) {W : ℕ} (hW : 0 < W) :
    ∃ S : Finset ℕ, S ⊆ A ∧
      (∀ a ∈ S, ∀ b ∈ S, a < b → a + W ≤ b) ∧
      ∀ a ∈ A, ∃ b ∈ S, a < b + W ∧ b < a + W := by
  classical
  let separated : Finset ℕ → Prop :=
    fun S => ∀ a ∈ S, ∀ b ∈ S, a < b → a + W ≤ b
  let candidates := A.powerset.filter separated
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, separated]
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image candidates Finset.card hne
  have hSA : S ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hsep : separated S := (Finset.mem_filter.mp hS).2
  refine ⟨S, hSA, hsep, ?_⟩
  intro a ha
  by_contra hn
  have hdis : ∀ b ∈ S, a + W ≤ b ∨ b + W ≤ a := by
    intro b hb
    by_contra h
    apply hn
    exact ⟨b, hb, by omega, by omega⟩
  have haS : a ∉ S := by
    intro haS
    rcases hdis a haS with h | h <;> omega
  have hnew : insert a S ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset ha hSA), ?_⟩
    intro x hx y hy hxy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · omega
      · rcases hdis y hy with h | h <;> omega
    · rcases hy with rfl | hy
      · rcases hdis x hx with h | h <;> omega
      · exact hsep x hx y hy hxy
  have h := hmax (insert a S) hnew
  rw [Finset.card_insert_of_notMem haS] at h
  omega

theorem cover_card_le_three_width
    (A S T : Finset ℕ) {W : ℕ} (hW : 0 < W)
    (hdom : ∀ a ∈ A, ∃ b ∈ S, a < b + W ∧ b < a + W)
    (hcover : ∀ x ∈ T, ∃ a ∈ A, a ≤ x ∧ x < a + W) :
    T.card ≤ 3 * W * S.card := by
  classical
  have hsub : T ⊆ S.biUnion (fun b => Finset.Ico (b - W) (b + 2 * W)) := by
    intro x hx
    obtain ⟨a, ha, hax, hxa⟩ := hcover x hx
    obtain ⟨b, hb, hab, hba⟩ := hdom a ha
    apply Finset.mem_biUnion.mpr
    exact ⟨b, hb, Finset.mem_Ico.mpr ⟨by omega, by omega⟩⟩
  calc
    T.card ≤ (S.biUnion (fun b => Finset.Ico (b - W) (b + 2 * W))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ S, (Finset.Ico (b - W) (b + 2 * W)).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ S, 3 * W := by
      apply Finset.sum_le_sum
      intro b hb
      rw [Nat.card_Ico]
      omega
    _ = 3 * W * S.card := by simp [Nat.mul_comm]

end Yau.Blueprint.Alignment.Y04Proof
