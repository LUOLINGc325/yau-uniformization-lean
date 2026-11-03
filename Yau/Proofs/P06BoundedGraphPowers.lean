import Yau.Proofs.P06GraphRegularization
import Yau.Proofs.P06SpectralBounds

noncomputable section
open ContinuousLinearMap
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem contraction_power_bound (S : H →L[ℝ] H) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (m : ℕ) (x : H) : ‖(S ^ m) x‖ ≤ ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact (hS _).trans ih

/-- Quantitative finite graph chains obtained from commuting bounded heat
and generator factors. Every membership is in the given actual graph. -/
theorem boundedGraph_power_chain (T : H →ₗ.[ℝ] H) (S E : H →L[ℝ] H)
    (hgraph : ∀ f, (S f, E f) ∈ T.graph) (hc : Commute S E)
    (C : ℝ) (hC : 0 ≤ C) (hS : ∀ x, ‖S x‖ ≤ ‖x‖)
    (hE : ∀ x, ‖E x‖ ≤ C * ‖x‖) (m : ℕ) (f : H) :
    ∃ u : ℕ → H, u 0 = (S ^ m) f ∧
      (∀ j, j < m → (u j, u (j + 1)) ∈ T.graph) ∧
      ∀ j, j ≤ m → ‖u j‖ ≤ C ^ j * ‖f‖ := by
  induction m generalizing f with
  | zero =>
    refine ⟨fun _ => f, by simp, ?_, ?_⟩
    · intro j hj
      omega
    · intro j hj
      have hj0 : j = 0 := by omega
      simp [hj0]
  | succ m ih =>
    obtain ⟨u, hu, hchain, hbound⟩ := ih (E f)
    let v : ℕ → H
      | 0 => (S ^ (m + 1)) f
      | j + 1 => u j
    refine ⟨v, rfl, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero =>
        change ((S ^ (m + 1)) f, u 0) ∈ T.graph
        rw [hu]
        have he : (S ^ m) (E f) = E ((S ^ m) f) :=
          congrArg (fun A : H →L[ℝ] H => A f) (hc.pow_left m).eq
        simpa only [pow_succ', mul_apply_eq_comp, he] using hgraph ((S ^ m) f)
      | succ j => exact hchain j (by omega)
    · intro j hj
      cases j with
      | zero =>
        simpa only [pow_zero, one_mul] using contraction_power_bound S hS (m + 1) f
      | succ j =>
        change ‖u j‖ ≤ C ^ (j + 1) * ‖f‖
        calc
          _ ≤ C ^ j * ‖E f‖ := hbound j (by omega)
          _ ≤ C ^ j * (C * ‖f‖) := mul_le_mul_of_nonneg_left (hE f) (pow_nonneg hC j)
          _ = _ := by rw [pow_succ]; ring

end Yau.NodeProofs.P06Aux
