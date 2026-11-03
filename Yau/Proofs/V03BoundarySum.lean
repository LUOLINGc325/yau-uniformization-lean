import Yau.Proofs.V03GagliardoVector
import Yau.Proofs.V03FiniteNormSum

/-! Finite sums and complex conjugation preserve the actual homogeneous
boundary seminorm estimates, including their infinite endpoints. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_sum_le {ι : Type*} [Fintype ι] {u : ι → ℝ → ℂ}
    (hu : ∀ i, Continuous (u i))
    (hp : ∀ i, Function.Periodic (u i) (2 * Real.pi)) :
    boundaryDSq (fun θ (_ : Unit) => ∑ i, u i θ) ≤
      (Fintype.card ι : ENNReal) * ∑ i, boundaryDSq (fun θ (_ : Unit) => u i θ) := by
  have hsum : Continuous (fun θ => ∑ i, u i θ) := continuous_finset_sum _ (fun i _ => hu i)
  have hperiod : Function.Periodic (fun θ => ∑ i, u i θ) (2 * Real.pi) := by
    intro θ
    exact Finset.sum_congr rfl (fun i _ => hp i θ)
  have hh := boundaryDSq_le_of_sum_square_bound (fun i => hu i) hsum hp hperiod
    (C := (Fintype.card ι : ℝ)) (by positivity) (fun θ t => by
      simpa only [← Finset.sum_sub_distrib, Finset.card_univ] using
        norm_sum_sq_le_card_mul_sum_norm_sq Finset.univ (fun i => u i θ - u i t))
  rw [boundaryDSq_eq_sum_singleton (fun θ i => u i θ)] at hh
  simpa only [ENNReal.ofReal_natCast] using hh

theorem scalarDSq_conj {u : ℝ → ℂ} (hu : Continuous u)
    (hp : Function.Periodic u (2 * Real.pi)) :
    boundaryDSq (fun θ (_ : Unit) => star (u θ)) = boundaryDSq (fun θ (_ : Unit) => u θ) := by
  have hc : Continuous (fun θ => star (u θ)) := hu.star
  have hpc : Function.Periodic (fun θ => star (u θ)) (2 * Real.pi) :=
    fun θ => congrArg star (hp θ)
  have h1 := boundaryDSq_le_of_difference_bound hu hc hp hpc (C := 1) (by norm_num)
    (fun θ t => by simp only [← star_sub, norm_star, one_mul]; exact le_rfl)
  have h2 := boundaryDSq_le_of_difference_bound hc hu hpc hp (C := 1) (by norm_num)
    (fun θ t => by simp only [← star_sub, norm_star, one_mul]; exact le_rfl)
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at h1 h2
  exact le_antisymm h1 h2

end Yau.Blueprint.V03Proof
