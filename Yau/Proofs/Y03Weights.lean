import Yau.Blueprint.Alignment

/-! Finite path propagation for Y03's literal predecessor maximum. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

theorem finite_path_loss {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ℕ → ι → ℝ) (loss : ℝ) (hloss : 0 ≤ loss)
    (hmono : ∀ i, Monotone (fun t => μ t i))
    {a b : ℕ × ι}
    (hpath : Relation.ReflTransGen (fun x y : ℕ × ι =>
      x.1 ≤ y.1 ∧ μ x.1 x.2 - loss ≤ μ y.1 y.2) a b) :
    μ a.1 a.2 ≤ μ b.1 b.2 + (Fintype.card ι : ℝ) * loss := by
  have hinv : ∃ (S : Finset ι) (m : ℝ), b.2 ∈ S ∧
      μ a.1 a.2 ≤ m + (S.card : ℝ) * loss ∧
      ∀ i ∈ S, m ≤ μ b.1 i := by
    induction hpath with
    | refl =>
      refine ⟨{a.2}, μ a.1 a.2, by simp, ?_, ?_⟩
      · simpa using hloss
      · intro i hi
        simp only [Finset.mem_singleton] at hi
        subst i
        exact le_rfl
    | @tail b c hpath hbc ih =>
      obtain ⟨S, m, hbS, hbound, hmin⟩ := ih
      have hprop : ∀ i ∈ S, m ≤ μ c.1 i :=
        fun i hi => (hmin i hi).trans (hmono i hbc.1)
      by_cases hdrop : μ c.1 c.2 < m
      · have hnew : c.2 ∉ S := fun hi => (not_le_of_gt hdrop) (hprop c.2 hi)
        refine ⟨insert c.2 S, μ c.1 c.2, by simp, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hnew, Nat.cast_add, Nat.cast_one]
          have hedge : m ≤ μ c.1 c.2 + loss := by
            have := hmin b.2 hbS
            linarith [hbc.2]
          nlinarith
        · intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi
          · exact le_rfl
          · exact hdrop.le.trans (hprop i hi)
      · refine ⟨insert c.2 S, m, by simp, ?_, ?_⟩
        · have hcard : (S.card : ℝ) ≤ (Finset.card (insert c.2 S) : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.subset_insert c.2 S)
          nlinarith
        · intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi
          · exact le_of_not_gt hdrop
          · exact hprop i hi
  obtain ⟨S, m, hbS, hbound, hmin⟩ := hinv
  have hcard : (S.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast Finset.card_le_univ S
  have hlast := hmin b.2 hbS
  nlinarith

theorem reach_rate_loss {n : ℕ} {p off : ℕ} {μ : ℕ → Fin n → ℝ}
    {eps θ : ℝ} (hloss : 0 ≤ eps * θ)
    (hmono : ∀ i, Monotone (fun t => μ t i))
    {a b : ℕ × Fin n} (hab : Reach p μ off eps θ a b) :
    μ (off + a.1) a.2 ≤ μ (off + b.1) b.2 + (n : ℝ) * (eps * θ) := by
  have hpath : Relation.ReflTransGen (fun x y : ℕ × Fin n =>
      x.1 ≤ y.1 ∧ μ (off + x.1) x.2 - eps * θ ≤ μ (off + y.1) y.2) a b := by
    induction hab with
    | refl => exact .refl
    | tail _ he ih =>
      exact ih.tail ⟨by rcases he.2.2.1 with h | h <;> omega, he.2.2.2⟩
  simpa only [Fintype.card_fin] using finite_path_loss (fun t i => μ (off + t) i)
    (eps * θ) hloss (fun i a b hab => hmono i (Nat.add_le_add_left hab off)) hpath

theorem rawWeight_le_propagatedWeight {n : ℕ} (p : ℕ) (μ : ℕ → Fin n → ℝ)
    (off : ℕ) (lam eps θ : ℝ) (b : ℕ × Fin n) :
    rawWeight μ off lam θ b ≤ propagatedWeight p μ off lam eps θ b := by
  unfold propagatedWeight
  exact Finset.le_sup' id (Finset.mem_insert_self _ _)

theorem propagatedWeight_upper {n : ℕ} (p : ℕ) (μ : ℕ → Fin n → ℝ)
    (off : ℕ) {lam eps θ : ℝ} (hlam : 0 ≤ lam) (hloss : 0 ≤ eps * θ)
    (hmono : ∀ i, Monotone (fun t => μ t i)) (b : ℕ × Fin n) :
    propagatedWeight p μ off lam eps θ b ≤
      lam * (μ (off + b.1) b.2 - θ + (n : ℝ) * (eps * θ)) := by
  unfold propagatedWeight
  apply Finset.sup'_le
  intro x hx
  rcases Finset.mem_insert.1 hx with rfl | hx
  · unfold rawWeight
    have hnonneg : 0 ≤ (n : ℝ) * (eps * θ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hlam
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    have hreach := (Finset.mem_filter.1 ha).2
    have hbound := reach_rate_loss hloss hmono hreach
    unfold rawWeight
    exact mul_le_mul_of_nonneg_left (by linarith) hlam

theorem propagatedWeight_mono_of_reach {n : ℕ} {p off : ℕ}
    {μ : ℕ → Fin n → ℝ} {lam eps θ : ℝ} {a b : ℕ × Fin n}
    (ha : a ∈ vertices p) (hab : Reach p μ off eps θ a b) :
    propagatedWeight p μ off lam eps θ a ≤ propagatedWeight p μ off lam eps θ b := by
  unfold propagatedWeight
  apply Finset.sup'_le
  intro x hx
  apply Finset.le_sup' id
  apply Finset.mem_insert.2
  rcases Finset.mem_insert.1 hx with rfl | hx
  · right
    exact Finset.mem_image.2 ⟨a, Finset.mem_filter.2 ⟨ha, hab⟩, rfl⟩
  · right
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_image.2 ⟨c,
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hc).1, ((Finset.mem_filter.1 hc).2).trans hab⟩,
      rfl⟩

theorem propagatedWeight_mono_of_passage {n : ℕ} {p off : ℕ}
    {μ : ℕ → Fin n → ℝ} {lam eps θ : ℝ} {a b : ℕ × Fin n}
    (ha : a ∈ vertices p) (hb : b ∈ vertices p) (hab : Passage μ off eps θ a b) :
    propagatedWeight p μ off lam eps θ a ≤ propagatedWeight p μ off lam eps θ b :=
  propagatedWeight_mono_of_reach ha (.tail .refl ⟨ha, hb, hab⟩)

theorem propagatedWeight_bounds {n : ℕ} (p : ℕ) (μ : ℕ → Fin n → ℝ)
    (off : ℕ) {lam eps θ : ℝ} (hlam : 0 ≤ lam) (heps : 0 ≤ eps) (hθ : 0 ≤ θ)
    (hsmall : (n : ℝ) * eps ≤ 0.1) (hmono : ∀ i, Monotone (fun t => μ t i))
    (b : ℕ × Fin n) :
    lam * (μ (off + b.1) b.2 - θ) ≤ propagatedWeight p μ off lam eps θ b ∧
      propagatedWeight p μ off lam eps θ b ≤ lam * (μ (off + b.1) b.2 - 0.9 * θ) := by
  refine ⟨rawWeight_le_propagatedWeight p μ off lam eps θ b, ?_⟩
  apply (propagatedWeight_upper p μ off hlam (mul_nonneg heps hθ) hmono b).trans
  apply mul_le_mul_of_nonneg_left _ hlam
  have hmul := mul_le_mul_of_nonneg_right hsmall hθ
  nlinarith

theorem forbidden_nonlinear_gap {n : ℕ} {μ w : Fin n → ℝ} {lam θ : ℝ}
    (hlam : 0 < lam) (hθ : 0 ≤ θ)
    (hlower : ∀ i, lam * (μ i - θ) ≤ w i)
    (hupper : ∀ i, w i ≤ lam * (μ i - 0.9 * θ))
    (i : Fin n) (β : Fin n →₀ ℕ) (hdegree : 2 ≤ β.sum (fun _ e => e))
    (hweight : w i < ∑ l, (β l : ℝ) * w l) :
    0.8 * θ < ∑ l, (β l : ℝ) * μ l - μ i := by
  have hdegNat : 2 ≤ ∑ l, β l := by
    rw [Finsupp.sum_fintype β (fun _ e => e) (fun _ => rfl)] at hdegree
    exact hdegree
  have hdeg : (2 : ℝ) ≤ ∑ l, (β l : ℝ) := by exact_mod_cast hdegNat
  have hsum : ∑ l, (β l : ℝ) * w l ≤
      lam * ((∑ l, (β l : ℝ) * μ l) - 0.9 * θ * (∑ l, (β l : ℝ))) := by
    calc
      _ ≤ ∑ l, (β l : ℝ) * (lam * (μ l - 0.9 * θ)) :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hupper l) (Nat.cast_nonneg _)
      _ = ∑ l, lam * ((β l : ℝ) * μ l - 0.9 * θ * (β l : ℝ)) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hstrict := (hlower i).trans_lt (hweight.trans_le hsum)
  have hcancel : μ i - θ < (∑ l, (β l : ℝ) * μ l) - 0.9 * θ * (∑ l, (β l : ℝ)) :=
    (mul_lt_mul_iff_right₀ hlam).1 hstrict
  nlinarith

theorem multiplier_zero (scale K : ℝ) : multiplier scale K 0 = scale := by
  simp [multiplier]

theorem multiplier_succ (scale K : ℝ) (j : ℕ) :
    multiplier scale K (j + 1) =
      multiplier scale K j * (1 + K / ((j + 1 : ℕ) : ℝ) ^ 2) := by
  simp only [multiplier, Finset.prod_range_succ]
  ring

theorem multiplier_pos {scale K : ℝ} (hscale : 0 < scale) (hK : 0 ≤ K) (j : ℕ) :
    0 < multiplier scale K j := by
  unfold multiplier
  apply mul_pos hscale
  exact Finset.prod_pos fun r _ => by positivity

theorem scale_le_multiplier {scale K : ℝ} (hscale : 0 ≤ scale) (hK : 0 ≤ K) (j : ℕ) :
    scale ≤ multiplier scale K j := by
  unfold multiplier
  have hprod : 1 ≤ ∏ r ∈ Finset.range j, (1 + K / ((r + 1 : ℕ) : ℝ) ^ 2) := by
    exact Finset.one_le_prod₀ fun r _ => le_add_of_nonneg_right (div_nonneg hK (sq_nonneg _))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hscale

theorem reciprocal_square_partial_sum (j : ℕ) :
    ∑ r ∈ Finset.range j, (1 : ℝ) / ((r + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
  have hsharp : ∀ m : ℕ,
      ∑ r ∈ Finset.range (m + 1), (1 : ℝ) / ((r + 1 : ℕ) : ℝ) ^ 2 ≤
        2 - 1 / ((m + 1 : ℕ) : ℝ) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h₁ : (0 : ℝ) < (m + 1 : ℕ) := by positivity
      have h₂ : (0 : ℝ) < (m + 1 + 1 : ℕ) := by positivity
      have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) -
          1 / ((m + 1 + 1 : ℕ) : ℝ) ≥ 1 / ((m + 1 + 1 : ℕ) : ℝ) ^ 2 := by
        push_cast
        field_simp
        nlinarith
      calc
        _ ≤ (2 - 1 / ((m + 1 : ℕ) : ℝ)) + 1 / ((m + 1 + 1 : ℕ) : ℝ) ^ 2 :=
          add_le_add ih le_rfl
        _ ≤ _ := by linarith
  cases j with
  | zero => simp
  | succ j => exact (hsharp j).trans (by linarith [one_div_nonneg.2 (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ (j + 1 : ℕ))])

theorem multiplier_bounded {scale K : ℝ} (hscale : 0 ≤ scale) (hK : 0 ≤ K) :
    ∃ B : ℝ, ∀ j, multiplier scale K j ≤ B := by
  refine ⟨scale * Real.exp (2 * K), fun j => ?_⟩
  unfold multiplier
  apply mul_le_mul_of_nonneg_left _ hscale
  calc
    _ ≤ Real.exp (∑ r ∈ Finset.range j, K / ((r + 1 : ℕ) : ℝ) ^ 2) := by
      apply Real.prod_one_add_le_exp_sum
      intro r
      positivity
    _ ≤ Real.exp (2 * K) := by
      apply Real.exp_le_exp.2
      have hsum := mul_le_mul_of_nonneg_left (reciprocal_square_partial_sum j) hK
      simpa only [Finset.mul_sum, mul_one_div, mul_comm K 2] using hsum

end Yau.Blueprint.Alignment.Y03Proof
