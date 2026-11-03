import Yau.Proofs.Y01EnvelopeAlgebra

/-! Finite closure operations for uniform sqrt-clock coefficient bounds.
All rates remain explicit real constants on the same clock sequence. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Yau.Proofs.Y02Aux

 theorem exists_constant_sqrt_envelope {s x : ℕ → ℝ} (hs : ∀ k, 1 ≤ s k)
    {K : ℝ} (hx : ∀ k, x k ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, x k ≤ Real.exp (C * Real.sqrt (s k)) := by
  refine ⟨max 0 K, le_max_left _ _, ?_⟩
  intro k
  exact (hx k).trans ((le_max_right _ _).trans (constant_le_sqrt_envelope (le_max_left _ _) (hs k)))

theorem exists_sum_sqrt_envelope {s x y : ℕ → ℝ} (hs : ∀ k, 1 ≤ s k)
    (hx : ∃ A : ℝ, 0 ≤ A ∧ ∀ k, x k ≤ Real.exp (A * Real.sqrt (s k)))
    (hy : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, y k ≤ Real.exp (B * Real.sqrt (s k))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, x k + y k ≤ Real.exp (C * Real.sqrt (s k)) := by
  obtain ⟨A, hA, hx⟩ := hx
  obtain ⟨B, hB, hy⟩ := hy
  refine ⟨max A B + Real.log 2, by positivity, ?_⟩
  intro k
  exact exp_sqrt_add_bound (hs k) (hx k) (hy k)

theorem exists_mul_sqrt_envelope {s x y : ℕ → ℝ}
    (hx0 : ∀ k, 0 ≤ x k) (hy0 : ∀ k, 0 ≤ y k)
    (hx : ∃ A : ℝ, 0 ≤ A ∧ ∀ k, x k ≤ Real.exp (A * Real.sqrt (s k)))
    (hy : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, y k ≤ Real.exp (B * Real.sqrt (s k))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, x k * y k ≤ Real.exp (C * Real.sqrt (s k)) := by
  obtain ⟨A, hA, hx⟩ := hx
  obtain ⟨B, hB, hy⟩ := hy
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro k
  exact mul_sqrt_envelope (hx0 k) (hy0 k) (hx k) (hy k)

theorem exists_pow_sqrt_envelope {s x : ℕ → ℝ} (hx0 : ∀ k, 0 ≤ x k)
    (hx : ∃ A : ℝ, 0 ≤ A ∧ ∀ k, x k ≤ Real.exp (A * Real.sqrt (s k))) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (x k) ^ m ≤ Real.exp (C * Real.sqrt (s k)) := by
  obtain ⟨A, hA, hx⟩ := hx
  refine ⟨(m : ℝ) * A, by positivity, ?_⟩
  intro k
  exact pow_sqrt_envelope (hx0 k) (hx k) m

theorem exists_jetComp_sqrt_envelope {n d : ℕ} {s : ℕ → ℝ} {P Q : ℕ → PolyMap n}
    (hs : ∀ k, 1 ≤ s k) (hdegree : ∀ k, (P k).degree ≤ d)
    (hP : ∃ A : ℝ, 0 ≤ A ∧ ∀ k, (P k).coeffNorm ≤ Real.exp (A * Real.sqrt (s k)))
    (hQ : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, (Q k).coeffNorm ≤ Real.exp (B * Real.sqrt (s k))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, (jetComp d (P k) (Q k)).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) := by
  obtain ⟨A, hA, hP⟩ := hP
  obtain ⟨B, hB, hQ⟩ := hQ
  refine ⟨A + (d : ℝ) * (max 0 B + Real.log 2), by positivity, ?_⟩
  intro k
  exact jetComp_sqrt_envelope (hs k) (hdegree k) (hP k) (hQ k)

theorem comp_sqrt_envelope {n d : ℕ} {s A B : ℝ} {P Q : PolyMap n}
    (hs : 1 ≤ s) (hdegree : P.degree ≤ d)
    (hP : P.coeffNorm ≤ Real.exp (A * Real.sqrt s))
    (hQ : Q.coeffNorm ≤ Real.exp (B * Real.sqrt s)) :
    (P.comp Q).coeffNorm ≤
      Real.exp ((A + (d : ℝ) * (max 0 B + Real.log 2)) * Real.sqrt s) := by
  have hbase : 1 ≤ 1 + Q.coeffNorm := by linarith [coeffNorm_nonneg Q]
  have hpow := pow_le_pow_right₀ hbase hdegree
  have hsum := one_add_sqrt_envelope hs hQ
  have hpowBound := pow_sqrt_envelope (by linarith [coeffNorm_nonneg Q]) hsum d
  exact (comp_coeffNorm_le P Q).trans
    ((mul_le_mul_of_nonneg_left hpow (coeffNorm_nonneg P)).trans
      (mul_sqrt_envelope (coeffNorm_nonneg P) (by positivity) hP hpowBound))

theorem exists_comp_sqrt_envelope {n d : ℕ} {s : ℕ → ℝ} {P Q : ℕ → PolyMap n}
    (hs : ∀ k, 1 ≤ s k) (hdegree : ∀ k, (P k).degree ≤ d)
    (hP : ∃ A : ℝ, 0 ≤ A ∧ ∀ k, (P k).coeffNorm ≤ Real.exp (A * Real.sqrt (s k)))
    (hQ : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, (Q k).coeffNorm ≤ Real.exp (B * Real.sqrt (s k))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ((P k).comp (Q k)).coeffNorm ≤ Real.exp (C * Real.sqrt (s k)) := by
  obtain ⟨A, hA, hP⟩ := hP
  obtain ⟨B, hB, hQ⟩ := hQ
  refine ⟨A + (d : ℝ) * (max 0 B + Real.log 2), by positivity, ?_⟩
  intro k
  exact comp_sqrt_envelope (hs k) (hdegree k) (hP k) (hQ k)

end Yau.Proofs.Y01Aux
