import Yau.Proofs.F05GeneralSchauderLocal
import Yau.Proofs.F05PositiveTimeBootstrap

/-! Compatible smooth data yield an actual local nonlinear Dirichlet
solution, with finite closed-corner Schauder regularity and full joint
smoothness on every positive-time closed physical receiving chart. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_dirichlet_local (hn : 0 < n) {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ) {S α : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S)) (hp : SmoothSpaceTime p (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (hα : 0 < α) (hα1 : α < 1)
    (hCompat : ∀ x, derivWithin (p x) (Icc 0 S) 0 =
      Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ S ∧ δ ≤ 1 ∧ 0 < K ∧ ∀ T : ℝ, 0 < T → T ≤ δ →
      ∃ w : M.Carrier → ℝ → ℝ,
        (∀ i, SchauderBound α (F05Q A i T) (pull A i w) K) ∧
        ContinuousOn (fun z : M.Carrier × ℝ => w z.1 z.2) (closure O ×ˢ Icc 0 T) ∧
        (∀ x ∈ closure O, w x 0 = p x 0) ∧
        (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = p x t) ∧
        (∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
          derivWithin (w x) (Icc 0 T) t =
            Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
              (1-Real.exp (-w x t))*scalarCurvature (h t) x) ∧
        ∀ τ : ℝ, 0 < τ → τ < T → ∀ i,
          ContDiffOn ℝ ∞ (pull A i w) (F05D A i ×ˢ Icc τ T) := by
  obtain ⟨δ,K,hδ,hδS,hδ1,hK,hSolve⟩ :=
    F05_schauder_nonlinear_local_general hA hχ h p hS hh hp hR hα hα1 hCompat
  refine ⟨δ,K,hδ,hδS,hδ1,hK,?_⟩
  intro T hT hTδ
  obtain ⟨w,hSch,hCont,hInitial,hBoundary,hEquation⟩ := hSolve T hT hTδ
  have hTS : Icc (0 : ℝ) T ⊆ Icc 0 S := fun t ht => ⟨ht.1,ht.2.trans (hTδ.trans hδS)⟩
  have hhT : MetricFamilySmooth h (Icc 0 T) := fun x a b =>
    (hh x a b).mono (prod_mono subset_rfl hTS)
  have hpT : SmoothSpaceTime p (Icc 0 T) := fun x => (hp x).mono (prod_mono subset_rfl hTS)
  have hRT : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T) :=
    fun x => (hR x).mono (prod_mono subset_rfl hTS)
  exact ⟨w,hSch,hCont,hInitial,hBoundary,hEquation,
    F05_positive_time_boundary_bootstrap hn hA h _ p w hT hα hα1 hhT hRT hpT
      hCont hSch hInitial hBoundary hEquation⟩

end Yau.Proofs.F05Aux
