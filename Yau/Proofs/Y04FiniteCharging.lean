import Yau.Proofs.Y04FlagIntervals

/-! Finite disjoint flag charging, including both finite boundary losses. -/

noncomputable section

open scoped BigOperators

namespace Yau.Blueprint.Alignment.Y04Proof

theorem disjoint_increment_sum_le
    (ell : ℕ → ℝ) (S : Finset ℕ) (u R q : ℕ)
    (huR : u ≤ R) (hmono : MonotoneOn ell (Set.Ici u))
    (hbounds : ∀ a ∈ S, u ≤ a ∧ a + q ≤ R)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a < b → a + q ≤ b) :
    (∑ a ∈ S, (ell (a + q) - ell a)) ≤ ell R - ell u := by
  classical
  induction S using Finset.induction_on_max generalizing R with
  | empty =>
    have h : ell u ≤ ell R := hmono (by simp) (by simpa using huR) huR
    simpa using sub_nonneg.mpr h
  | insert a S hmax ih =>
    have ha : a ∉ S := by intro h; exact (hmax a h).false
    have hau := (hbounds a (Finset.mem_insert_self a S)).1
    have haR := (hbounds a (Finset.mem_insert_self a S)).2
    have hS : (∑ b ∈ S, (ell (b + q) - ell b)) ≤ ell a - ell u := by
      apply ih a hau
      · intro b hb
        exact ⟨(hbounds b (Finset.mem_insert_of_mem hb)).1,
          hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self a S) (hmax b hb)⟩
      · intro b hb c hc hbc
        exact hsep b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc) hbc
    rw [Finset.sum_insert ha]
    have hend := hmono (by omega : u ≤ a + q) huR haR
    linarith

theorem finite_flag_charge
    (Q : ℕ → ℝ) (N : ℕ) (M : ℝ) (u R : ℕ)
    (A T : Finset ℕ) (hM : 0 < M) (huR : u ≤ R)
    (hmono : MonotoneOn Q (Set.Ici u))
    (hpos : ∀ r, u ≤ r → 0 < Q r)
    (hflags : ∀ a ∈ A,
      u ≤ a ∧ a + N + 1 ≤ R ∧ flagStart Q N M a)
    (hcover : ∀ x ∈ T,
      ∃ a ∈ A, a ≤ x ∧ x < a + (2 * N + 1)) :
    (M / (3 * (2 * N + 1 : ℝ))) * (T.card : ℝ) ≤
      Real.log (Q R / Q u) := by
  classical
  obtain ⟨S, hSA, hsep, hdom⟩ :=
    select_disjoint_equal_intervals A (W := 2 * N + 1) (by omega)
  have hcard := cover_card_le_three_width A S T (by omega : 0 < 2 * N + 1) hdom hcover
  have hcardR : (T.card : ℝ) ≤ (3 * (2 * N + 1 : ℝ)) * S.card := by
    exact_mod_cast hcard
  have hlogmono : MonotoneOn (fun r => Real.log (Q r)) (Set.Ici u) := by
    intro a ha b hb hab
    exact Real.log_le_log (hpos a ha) (hmono ha hb hab)
  have hsum : (S.card : ℝ) * M ≤
      ∑ a ∈ S, (Real.log (Q (a + N + 1)) - Real.log (Q a)) := by
    calc
      _ = ∑ _a ∈ S, M := by simp
      _ ≤ _ := Finset.sum_le_sum (fun a ha => le_of_lt (hflags a (hSA ha)).2.2)
  have htel := disjoint_increment_sum_le (fun r => Real.log (Q r)) S u R (N + 1)
    huR hlogmono
    (fun a ha => ⟨(hflags a (hSA ha)).1, by simpa [Nat.add_assoc] using (hflags a (hSA ha)).2.1⟩)
    (fun a ha b hb hab => by have := hsep a ha b hb hab; omega)
  have hden : 0 < 3 * (2 * N + 1 : ℝ) := by positivity
  calc
    _ ≤ (M / (3 * (2 * N + 1 : ℝ))) *
        ((3 * (2 * N + 1 : ℝ)) * S.card) :=
      mul_le_mul_of_nonneg_left hcardR (le_of_lt (div_pos hM hden))
    _ = (S.card : ℝ) * M := by field_simp
    _ ≤ _ := hsum.trans (by simpa [Nat.add_assoc] using htel)
    _ = _ := by rw [Real.log_div (ne_of_gt (hpos R huR)) (ne_of_gt (hpos u le_rfl))]

theorem full_bad_log_growth
    {Q : ℕ → ℝ} {jBound N u v : ℕ} {M : ℝ}
    (hM : 0 < M) (hmono : MonotoneOn Q (Set.Ici jBound))
    (hpos : ∀ j, jBound ≤ j → 0 < Q j)
    (hu : jBound ≤ u) (hc : FullBadComponent Q N M u v) :
    (M / (3 * (2 * N + 1 : ℝ))) * ((v-u : ℕ) : ℝ) ≤
      Real.log (Q (v-N) / Q u) := by
  classical
  let A := (Finset.Ico u v).filter (fun a => flagStart Q N M a ∧ a + (2 * N + 1) ≤ v)
  have hlen := fullBadComponent_length hc
  have h := finite_flag_charge Q N M u (v - N) A (Finset.Ico u v) hM (by omega)
    (hmono.mono (by intro r hr; exact hu.trans hr)) (fun r hr => hpos r (hu.trans hr))
    (by
      intro a ha
      obtain ⟨haI, haf, har⟩ := Finset.mem_filter.mp ha
      exact ⟨(Finset.mem_Ico.mp haI).1, by omega, haf⟩)
    (by
      intro x hx
      obtain ⟨hux, hxv⟩ := Finset.mem_Ico.mp hx
      obtain ⟨a, ha, hax, hxa⟩ := bad_iff_flagStart.mp (hc.2.2.2 x hux hxv)
      obtain ⟨hua, hav⟩ := flagStart_inside_full hc hux hxv ha hax hxa
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hua, by omega⟩, ha, hav⟩, hax, hxa⟩)
  simpa only [Nat.card_Ico] using h

theorem bad_prefix_log_growth
    {Q : ℕ → ℝ} {jBound N u j : ℕ} {M : ℝ}
    (hM : 0 < M) (hmono : MonotoneOn Q (Set.Ici jBound))
    (hpos : ∀ r, jBound ≤ r → 0 < Q r)
    (hu : jBound ≤ u) (huj : u ≤ j)
    (hleft : u = 0 ∨ Regular Q N M (u-1))
    (hbad : ∀ r, u ≤ r → r < j → Bad Q N M r) :
    (M / (3 * (2 * N + 1 : ℝ))) * ((j-u-(2*N+1) : ℕ) : ℝ) ≤
      Real.log (Q j / Q u) := by
  classical
  let W := 2 * N + 1
  let A := (Finset.Ico u j).filter (fun a => flagStart Q N M a ∧ a + W ≤ j)
  have h := finite_flag_charge Q N M u j A (Finset.Ico u (j - W)) hM huj
    (hmono.mono (by intro r hr; exact hu.trans hr)) (fun r hr => hpos r (hu.trans hr))
    (by
      intro a ha
      obtain ⟨haI, haf, har⟩ := Finset.mem_filter.mp ha
      refine ⟨(Finset.mem_Ico.mp haI).1, ?_, haf⟩
      dsimp [W] at har
      omega)
    (by
      intro x hx
      obtain ⟨hux, hxj⟩ := Finset.mem_Ico.mp hx
      have hxj' : x < j := by omega
      obtain ⟨a, ha, hax, hxa⟩ := bad_iff_flagStart.mp (hbad x hux hxj')
      have hua := flagStart_left_of_boundary hleft hux ha hax hxa
      have haj : a + W ≤ j := by omega
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hua, by omega⟩, ha, haj⟩, hax, hxa⟩)
  have hcard : (Finset.Ico u (j-W)).card = j-u-W := by rw [Nat.card_Ico]; omega
  simpa only [hcard, W] using h

theorem bad_interior_log_growth
    {Q : ℕ → ℝ} {jBound N a j : ℕ} {M : ℝ}
    (hM : 0 < M) (hmono : MonotoneOn Q (Set.Ici jBound))
    (hpos : ∀ r, jBound ≤ r → 0 < Q r)
    (ha : jBound ≤ a) (haj : a ≤ j)
    (hbad : ∀ r, a ≤ r → r < j → Bad Q N M r) :
    (M / (3 * (2 * N + 1 : ℝ))) *
        ((j-a-2*(2*N+1) : ℕ) : ℝ) ≤ Real.log (Q j / Q a) := by
  classical
  let W := 2 * N + 1
  let A := (Finset.Ico a j).filter (fun r => flagStart Q N M r ∧ r + W ≤ j)
  have h := finite_flag_charge Q N M a j A (Finset.Ico (a+W) (j-W)) hM haj
    (hmono.mono (by intro r hr; exact ha.trans hr)) (fun r hr => hpos r (ha.trans hr))
    (by
      intro r hr
      obtain ⟨hrI, hrf, hrr⟩ := Finset.mem_filter.mp hr
      refine ⟨(Finset.mem_Ico.mp hrI).1, ?_, hrf⟩
      dsimp [W] at hrr
      omega)
    (by
      intro x hx
      obtain ⟨hax, hxj⟩ := Finset.mem_Ico.mp hx
      have hxa : a ≤ x := by omega
      have hxj' : x < j := by omega
      obtain ⟨r, hr, hrx, hxr⟩ := bad_iff_flagStart.mp (hbad x hxa hxj')
      have har : a ≤ r := by dsimp [W] at hax; omega
      have hrj : r + W ≤ j := by omega
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨har, by omega⟩, hr, hrj⟩, hrx, hxr⟩)
  have hcard : (Finset.Ico (a+W) (j-W)).card = j-a-2*W := by rw [Nat.card_Ico]; omega
  simpa only [hcard, W] using h

end Yau.Blueprint.Alignment.Y04Proof
