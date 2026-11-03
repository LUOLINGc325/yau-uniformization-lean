import Yau.Proofs.Y06BoundedSubsequence

/-! One subsequence simultaneously compactifies the four literal JetData families. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter Yau.Blueprint.Alignment
open scoped Topology

variable {n : ℕ}

def JetDataDegreeBound (D : ℕ) (Q : JetData n) : Prop :=
  ∀ k, (Q.correction k).degree ≤ D ∧ (Q.inverseJet k).degree ≤ D ∧
    (Q.model k).degree ≤ D ∧ (Q.inverseModel k).degree ≤ D

def JetDataNormBound (B : ℕ → ℝ) (Q : JetData n) : Prop :=
  ∀ k, (Q.correction k).coeffNorm ≤ B k ∧ (Q.inverseJet k).coeffNorm ≤ B k ∧
    (Q.model k).coeffNorm ≤ B k ∧ (Q.inverseModel k).coeffNorm ≤ B k

def JetDataCoefficientTendsto (Q : ℕ → JetData n) (R : JetData n) : Prop :=
  ∀ k i β,
    Tendsto (fun H => (Q H |>.correction k i).coeff β) atTop (𝓝 ((R.correction k i).coeff β)) ∧
    Tendsto (fun H => (Q H |>.inverseJet k i).coeff β) atTop (𝓝 ((R.inverseJet k i).coeff β)) ∧
    Tendsto (fun H => (Q H |>.model k i).coeff β) atTop (𝓝 ((R.model k i).coeff β)) ∧
    Tendsto (fun H => (Q H |>.inverseModel k i).coeff β) atTop (𝓝 ((R.inverseModel k i).coeff β))

def jetDataFamily (Q : JetData n) (t : Fin 4 × ℕ) : PolyMap n :=
  if t.1 = 0 then Q.correction t.2 else if t.1 = 1 then Q.inverseJet t.2 else
    if t.1 = 2 then Q.model t.2 else Q.inverseModel t.2

theorem jetData_subsequence (Q : ℕ → JetData n) (D : ℕ) (B : ℕ → ℝ)
    (hdegree : ∀ H, JetDataDegreeBound D (Q H)) (hbound : ∀ H, JetDataNormBound B (Q H)) :
    ∃ (R : JetData n) (σ : ℕ → ℕ), StrictMono σ ∧ JetDataDegreeBound D R ∧
      JetDataCoefficientTendsto (fun H => Q (σ H)) R ∧ JetDataNormBound B R := by
  have hdeg : ∀ H t, (jetDataFamily (Q H) t).degree ≤ D := by
    intro H ⟨t, k⟩
    fin_cases t <;> simp only [jetDataFamily] <;> norm_num
    · exact (hdegree H k).1
    · exact (hdegree H k).2.1
    · exact (hdegree H k).2.2.1
    · exact (hdegree H k).2.2.2
  have hnorm : ∀ H t, (jetDataFamily (Q H) t).coeffNorm ≤ B t.2 := by
    intro H ⟨t, k⟩
    fin_cases t <;> simp [jetDataFamily]
    · exact (hbound H k).1
    · exact (hbound H k).2.1
    · exact (hbound H k).2.2.1
    · exact (hbound H k).2.2.2
  obtain ⟨q, σ, hσ, hqd, hlim, hqb⟩ := bounded_degree_polynomial_subsequence
    (fun H t => jetDataFamily (Q H) t) D (fun t => B t.2) hdeg hnorm
  let R : JetData n := ⟨fun k => q (0, k), fun k => q (1, k), fun k => q (2, k), fun k => q (3, k)⟩
  refine ⟨R, σ, hσ, ?_, ?_, ?_⟩
  · intro k
    exact ⟨hqd (0, k), hqd (1, k), hqd (2, k), hqd (3, k)⟩
  · intro k i β
    exact ⟨by simpa [jetDataFamily, R] using hlim (0, k) i β,
      by simpa [jetDataFamily, R] using hlim (1, k) i β,
      by simpa [jetDataFamily, R] using hlim (2, k) i β,
      by simpa [jetDataFamily, R] using hlim (3, k) i β⟩
  · intro k
    exact ⟨hqb (0, k), hqb (1, k), hqb (2, k), hqb (3, k)⟩

end Yau.Proofs.Y06Aux
