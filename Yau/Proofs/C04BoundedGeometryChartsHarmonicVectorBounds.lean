import Yau.Proofs.C04BoundedGeometryChartsVectorJetBounds

/-! All orders for the same vector coordinate function follow from the fixed elliptic estimates. -/
noncomputable section
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem exists_harmonic_vector_derivative_bounds (n : ℕ) (ell : ℝ) (hell : 0 < ell)
    (A : ℕ → ℝ) (hA : ∀ s, 0 < A s) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
      ∀ (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
        (b : ComplexVector n → RIdx n → ℝ),
        (∀ i j, ContDiffOn ℝ ∞ (fun z => a z i j) (Metric.ball 0 (3 / 8 : ℝ))) →
        (∀ i, ContDiffOn ℝ ∞ (fun z => b z i) (Metric.ball 0 (3 / 8 : ℝ))) →
        (∀ z ∈ Metric.ball 0 (3 / 8 : ℝ), (a z).IsSymm ∧
          ∀ v : RIdx n → ℝ, ell * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, a z i j * v i * v j) →
        (∀ s k, k ≤ s + 1 → ∀ z ∈ Metric.ball 0 (3 / 8 : ℝ), ∀ i j,
          ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A s ∧
          ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A s) →
        ∀ F : ComplexVector n → ComplexVector n, ContDiff ℝ ∞ F →
          (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ‖F x‖ ≤ 1) →
          (∀ j : Fin n, Set.EqOn (Yau.LeafCandidates.ellipticOp a b (fun y => F y j)) 0
            (Metric.ball 0 (3 / 8 : ℝ))) →
          ∀ m x, x ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ) →
            ‖iteratedFDeriv ℝ m F x‖ ≤ D m := by
  let U := (lebesgueC n (Metric.ball (0 : ComplexVector n) (3 / 8 : ℝ))).toReal
  obtain ⟨Ds, hDs, hbound⟩ := exists_harmonic_derivative_bounds n ell U hell ENNReal.toReal_nonneg A hA
  refine ⟨fun m => 1 + (n : ℝ) * Ds m, fun m => by have h := hDs m; positivity, ?_⟩
  intro a b ha hb hEll hCoeff F hF hnorm hPDE m x hx
  have hcomponents (j : Fin n) : ‖iteratedFDeriv ℝ m (fun y => F y j) x‖ ≤ Ds m := by
    have hFj : ContDiff ℝ ∞ (fun y => F y j) := by
      let pr : ComplexVector n →L[ℝ] ℂ := (EuclideanSpace.proj j).restrictScalars ℝ
      change ContDiff ℝ ∞ (pr ∘ F)
      exact pr.contDiff.comp hF
    exact hbound a b ha hb hEll hCoeff _ hFj (coordinate_component_mass_bound F hF hnorm j)
      (hPDE j) m x hx
  exact (norm_vector_iteratedFDeriv_le_dimension F hF m x hcomponents).trans (by linarith)

end Yau.Proofs.C04ChartsAux
