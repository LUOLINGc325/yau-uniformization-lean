import Yau.Proofs.Y06BoundedCoefficients

/-! One coefficientwise subsequence for all four bounded-degree polynomial
families and every grid index, using a single countable coefficient index. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Filter Yau.Proofs.Y02Aux
open scoped Topology

theorem bounded_degree_polynomial_subsequence {n : ℕ} {ι : Type*} [Countable ι]
    (p : ℕ → ι → PolyMap n) (D : ℕ) (B : ι → ℝ)
    (hdegree : ∀ H k, (p H k).degree ≤ D) (hbound : ∀ H k, (p H k).coeffNorm ≤ B k) :
    ∃ (q : ι → PolyMap n) (subseq : ℕ → ℕ), StrictMono subseq ∧
      (∀ k, (q k).degree ≤ D) ∧
      (∀ k i β, Tendsto (fun H => (p (subseq H) k i).coeff β) atTop (𝓝 ((q k i).coeff β))) ∧
      ∀ k, (q k).coeffNorm ≤ B k := by
  let z := fun H (t : ι × Fin n × (Fin n →₀ ℕ)) => (p H t.1 t.2.1).coeff t.2.2
  have hz : ∀ H t, ‖z H t‖ ≤ B t.1 := by
    intro H t
    exact (coefficient_norm_le_coeffNorm (p H t.1) t.2.1 t.2.2).trans (hbound H t.1)
  obtain ⟨a, subseq, hstrict, hlim, hcoord, hnorm⟩ :=
    common_complex_coefficient_subsequence z (fun t => B t.1) hz
  let q := fun k => coefficientPolynomial D (fun i β => a (k, i, β))
  have hqdegree k : (q k).degree ≤ D := coefficientPolynomial_degree D _
  have hcoeff k i β : Tendsto (fun H => (p (subseq H) k i).coeff β) atTop (𝓝 ((q k i).coeff β)) := by
    change Tendsto _ atTop (𝓝 ((coefficientPolynomial D (fun i β => a (k, i, β)) i).coeff β))
    rw [coefficientPolynomial_coeff]
    by_cases hβ : β.degree ≤ D
    · rw [ite_eq_left hβ]
      exact hcoord (k, i, β)
    · rw [ite_eq_right hβ]
      have hzero : (fun H => (p (subseq H) k i).coeff β) = (fun _ => 0) :=
        funext (fun H => coeff_zero_of_degree_gt (hdegree (subseq H) k) i β hβ)
      rw [hzero]
      exact tendsto_const_nhds
  refine ⟨q, subseq, hstrict, hqdegree, hcoeff, ?_⟩
  intro k
  have ht := coeffNorm_tendsto_of_bounded_degree (D := D) (fun i => hcoeff k i)
    (fun H => hdegree (subseq H) k) (hqdegree k)
  exact le_of_tendsto ht (Eventually.of_forall (fun H => hbound (subseq H) k))

end Yau.Proofs.Y06Aux
