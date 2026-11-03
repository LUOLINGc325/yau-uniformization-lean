import Yau.Proofs.C07InverseSelection
import Yau.Proofs.C07InverseCompatibility

/-! The selected physical-time inverse has the actual geometry of its chosen local branch. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem selectedInverse_continuousOn
    (V : ℕ → Set M.Carrier) (T : ℕ → ℝ)
    (B : ℕ → ℝ → M.Carrier → ComplexVector n)
    (hB : ∀ j t, T j ≤ t → ContinuousOn (B j t) (V j)) (t : ℝ) :
    ContinuousOn (selectedInverse V T B t) (selectedInverseDomain V T t) := by
  classical
  by_cases ht : T 0 ≤ t
  · rw [selectedInverseDomain, ite_eq_left ht]
    apply (hB _ _ (lateIndex_eligible T ht)).congr
    intro x hx
    simp [selectedInverse, selectedInverseDomain, ht, hx]
  · simp only [selectedInverseDomain, ite_eq_right ht]
    exact continuousOn_empty (f := selectedInverse V T B t)

theorem selectedInverse_point
    (V : ℕ → Set M.Carrier) (T : ℕ → ℝ)
    (B : ℕ → ℝ → M.Carrier → ComplexVector n)
    (Φ : ℝ → ComplexVector n → M.Carrier) (r : ℝ)
    (hB : ∀ j t, T j ≤ t → ∀ x ∈ V j,
      B j t x ∈ Metric.ball 0 r ∧ Φ t (B j t x) = x)
    (t : ℝ) {x : M.Carrier} (hx : x ∈ selectedInverseDomain V T t) :
    selectedInverse V T B t x ∈ Metric.ball 0 r ∧ Φ t (selectedInverse V T B t x) = x := by
  classical
  by_cases ht : T 0 ≤ t
  · have hx' : x ∈ V (lateIndex T t) := by
      simpa only [selectedInverseDomain, ite_eq_left ht] using hx
    rw [selectedInverse_eq V T B hx]
    exact hB _ _ (lateIndex_eligible T ht) x hx'
  · have : False := by simpa [selectedInverseDomain, ht] using hx
    exact this.elim

theorem selectedInverse_mdifferentiable
    (V : ℕ → Set M.Carrier) (T : ℕ → ℝ)
    (B : ℕ → ℝ → M.Carrier → ComplexVector n)
    (Φ : ℝ → ComplexVector n → M.Carrier) {r R t₀ : ℝ} (hrR : r ≤ R)
    (hV : ∀ j, IsOpen (V j)) (hT : ∀ j, t₀ ≤ T j)
    (hΦ : ∀ t, t₀ ≤ t → IsLocalBiholomorphism (Φ t) R)
    (hBc : ∀ j t, T j ≤ t → ContinuousOn (B j t) (V j))
    (hBp : ∀ j t, T j ≤ t → ∀ x ∈ V j,
      B j t x ∈ Metric.ball 0 r ∧ Φ t (B j t x) = x) (t : ℝ) :
    MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n)
      (selectedInverse V T B t) (selectedInverseDomain V T t) := by
  classical
  by_cases ht : T 0 ≤ t
  · apply continuous_manifold_inverse_mdifferentiable
      (hΦ t ((hT _).trans (lateIndex_eligible T ht)))
      (selectedInverseDomain_open V T hV t) (selectedInverse_continuousOn V T B hBc t)
    · intro x hx
      exact Metric.ball_subset_ball hrR (selectedInverse_point V T B Φ r hBp t hx).1
    · intro x hx
      exact (selectedInverse_point V T B Φ r hBp t hx).2
  · simp only [selectedInverseDomain, ite_eq_right ht]
    exact mdifferentiableOn_empty

end Yau.Proofs.C07Aux
