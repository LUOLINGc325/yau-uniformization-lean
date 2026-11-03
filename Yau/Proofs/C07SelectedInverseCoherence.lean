import Yau.Proofs.C07SelectedInverseGeometry

/-! Connected-domain lift uniqueness makes the selected actual inverses agree and intertwine. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set

variable {n : ℕ} {M : ComplexManifold n}

theorem selectedInverse_branch_agreement
    (V : ℕ → Set M.Carrier) (T : ℕ → ℝ)
    (B : ℕ → ℝ → M.Carrier → ComplexVector n)
    (Φ : ℝ → ComplexVector n → M.Carrier) {o : M.Carrier} {r R : ℝ} (hrR : r ≤ R)
    (hV : Monotone V) (hVc : ∀ j, IsPreconnected (V j)) (ho : ∀ j, o ∈ V j)
    (hmajor : ∀ j : ℕ, (j : ℝ) ≤ T j)
    (hBc : ∀ j t, T j ≤ t → ContinuousOn (B j t) (V j))
    (hBp : ∀ j t, T j ≤ t → ∀ x ∈ V j,
      B j t x ∈ Metric.ball 0 r ∧ Φ t (B j t x) = x)
    (hB₀ : ∀ j t, T j ≤ t → B j t o = 0)
    {j : ℕ} {t : ℝ} (ht₀ : T 0 ≤ t) (htj : T j ≤ t)
    (hΦ : IsLocalBiholomorphism (Φ t) R) :
    EqOn (selectedInverse V T B t) (B j t) (V j) := by
  classical
  have hsub : V j ⊆ selectedInverseDomain V T t := by
    simpa only [selectedInverseDomain, ite_eq_left ht₀] using
      hV (le_lateIndex T hmajor htj)
  apply manifold_inverse_branches_unique hΦ (hVc j) (ho j)
    ((selectedInverse_continuousOn V T B hBc t).mono hsub) (hBc j t htj)
  · intro x hx
    exact Metric.ball_subset_ball hrR (selectedInverse_point V T B Φ r hBp t (hsub hx)).1
  · intro x hx
    exact Metric.ball_subset_ball hrR (hBp j t htj x hx).1
  · intro x hx
    exact (selectedInverse_point V T B Φ r hBp t (hsub hx)).2
  · intro x hx
    exact (hBp j t htj x hx).2
  · exact selectedInverse_zero V T B o ho hB₀ t
  · exact hB₀ j t htj

theorem selectedInverse_transition_coherence
    (V : ℕ → Set M.Carrier) (T : ℕ → ℝ)
    (B : ℕ → ℝ → M.Carrier → ComplexVector n)
    (Φ : ℝ → ComplexVector n → M.Carrier) {o : M.Carrier} {r R : ℝ} (hrR : r ≤ R)
    (hV : Monotone V) (hVc : ∀ j, IsPreconnected (V j)) (ho : ∀ j, o ∈ V j)
    (hBc : ∀ j t, T j ≤ t → ContinuousOn (B j t) (V j))
    (hBp : ∀ j t, T j ≤ t → ∀ x ∈ V j,
      B j t x ∈ Metric.ball 0 r ∧ Φ t (B j t x) = x)
    (hB₀ : ∀ j t, T j ≤ t → B j t o = 0)
    {t u : ℝ} (ht₀ : T 0 ≤ t) (htu : t ≤ u)
    (hΦ : IsLocalBiholomorphism (Φ u) R)
    (F : ComplexVector n → ComplexVector n) (hF : ContinuousOn F (Metric.ball 0 r))
    (hFball : ∀ z ∈ Metric.ball 0 r, F z ∈ Metric.ball 0 R)
    (hFproj : ∀ z ∈ Metric.ball 0 r, Φ u (F z) = Φ t z) (hF₀ : F 0 = 0) :
    EqOn (selectedInverse V T B u) (F ∘ selectedInverse V T B t)
      (selectedInverseDomain V T t) := by
  classical
  have hVc' : IsPreconnected (selectedInverseDomain V T t) := by
    simpa only [selectedInverseDomain, ite_eq_left ht₀] using hVc (lateIndex T t)
  have ho' : o ∈ selectedInverseDomain V T t := by
    simpa only [selectedInverseDomain, ite_eq_left ht₀] using ho (lateIndex T t)
  have hsub := selectedInverseDomain_monotone V T hV htu
  apply inverse_transition_coherence hΦ hVc' ho'
    (selectedInverse_continuousOn V T B hBc t)
    ((selectedInverse_continuousOn V T B hBc u).mono hsub) hF
  · intro x hx
    exact (selectedInverse_point V T B Φ r hBp t hx).1
  · intro x hx
    exact Metric.ball_subset_ball hrR (selectedInverse_point V T B Φ r hBp u (hsub hx)).1
  · exact hFball
  · intro x hx
    exact (selectedInverse_point V T B Φ r hBp t hx).2
  · intro x hx
    exact (selectedInverse_point V T B Φ r hBp u (hsub hx)).2
  · exact hFproj
  · exact selectedInverse_zero V T B o ho hB₀ t
  · exact selectedInverse_zero V T B o ho hB₀ u
  · exact hF₀

end Yau.Proofs.C07Aux
