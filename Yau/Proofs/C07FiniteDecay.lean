import Yau.Proofs.C07DecayNormalization

/-! A finite collection of genuine local exponential estimates has one positive rate. -/

open Filter
open scoped Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Set

variable {ι A G : Type*} [NormedAddCommGroup G]

theorem finite_uniform_exponential_bound (I : Finset ι) (s : ℝ → ℝ)
    (hs : Tendsto s atTop atTop) (V : ι → Set A) (f : ι → ℝ → A → G)
    (a B T : ι → ℝ) (ha : ∀ i ∈ I, 0 < a i) (hB : ∀ i ∈ I, 0 ≤ B i)
    (hbound : ∀ i ∈ I, ∀ t, T i ≤ t → ∀ x ∈ V i,
      ‖f i t x‖ ≤ B i * Real.exp (-a i * s t)) :
    ∃ b D S : ℝ, 0 < b ∧ 0 ≤ D ∧ ∀ t, S ≤ t →
      ∀ i ∈ I, ∀ x ∈ V i, ‖f i t x‖ ≤ D * Real.exp (-b * s t) := by
  classical
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp (hs.eventually (eventually_ge_atTop 0))
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨1, 0, S₀, zero_lt_one, le_rfl, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨b, D, S, hb, hD, hdecay⟩ := ih
      (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hB j (Finset.mem_insert_of_mem hj))
      (fun j hj => hbound j (Finset.mem_insert_of_mem hj))
    have hai : 0 < a i := ha i (Finset.mem_insert_self _ _)
    have hBi : 0 ≤ B i := hB i (Finset.mem_insert_self _ _)
    refine ⟨min (a i) b, max (B i) D, max S₀ (max (T i) S),
      lt_min hai hb, hBi.trans (le_max_left _ _), ?_⟩
    intro t ht j hj x hx
    have hs0 : 0 ≤ s t := hS₀ t ((le_max_left _ _).trans ht)
    have hti : T i ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
    have htS : S ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
    rcases Finset.mem_insert.mp hj with hji | hj
    · subst j
      calc
        ‖f i t x‖ ≤ B i * Real.exp (-a i * s t) := hbound i (Finset.mem_insert_self _ _) t hti x hx
        _ ≤ max (B i) D * Real.exp (-(min (a i) b) * s t) :=
          mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr
            (by nlinarith [min_le_left (a i) b])) (Real.exp_pos _).le
            (hBi.trans (le_max_left _ _))
    · calc
        ‖f j t x‖ ≤ D * Real.exp (-b * s t) := hdecay t htS j hj x hx
        _ ≤ max (B i) D * Real.exp (-(min (a i) b) * s t) :=
          mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr
            (by nlinarith [min_le_right (a i) b])) (Real.exp_pos _).le
            (hD.trans (le_max_right _ _))

end Yau.Proofs.C07Aux
