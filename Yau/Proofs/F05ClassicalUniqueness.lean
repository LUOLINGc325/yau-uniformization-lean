import Yau.Proofs.F05ClassicalBounds

/-! Actual compact closed-slab continuity and the original C2 fields
supply all comparison budgets internally. Classical nonlinear solutions
with the same parabolic data are unique on the supplied compact domain. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_classical_solution_unique {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {T : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T))
    (u v : M.Carrier → ℝ → ℝ)
    (hUCont : ContinuousOn (fun z : M.Carrier × ℝ => u z.1 z.2) (closure O ×ˢ Icc 0 T))
    (hVCont : ContinuousOn (fun z : M.Carrier × ℝ => v z.1 z.2) (closure O ×ˢ Icc 0 T))
    (hU : ∀ i, C2 (F05Q A i T) (pull A i u)) (hV : ∀ i, C2 (F05Q A i T) (pull A i v))
    (hInitial : ∀ x ∈ closure O, u x 0 = v x 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u x t = v x t)
    (hUEq : ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (u x) (Icc 0 T) t = Real.exp (-u x t)*laplacian (h t) (fun y => u y t) x+
        (1-Real.exp (-u x t))*scalarCurvature (h t) x)
    (hVEq : ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (v x) (Icc 0 T) t = Real.exp (-v x t)*laplacian (h t) (fun y => v y t) x+
        (1-Real.exp (-v x t))*scalarCurvature (h t) x) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, u x t = v x t := by
  have hUV := F05_classical_comparison hA h hT hh hR u v hUCont hVCont hU hV
    (fun x hx => (hInitial x hx).le) (fun x hx t ht => (hBoundary x hx t ht).le)
    (fun x hx t ht => (hUEq x (subset_closure hx) t ⟨ht.1.le,ht.2⟩).le)
    (fun x hx t ht => (hVEq x (subset_closure hx) t ⟨ht.1.le,ht.2⟩).ge)
  have hVU := F05_classical_comparison hA h hT hh hR v u hVCont hUCont hV hU
    (fun x hx => (hInitial x hx).ge) (fun x hx t ht => (hBoundary x hx t ht).ge)
    (fun x hx t ht => (hVEq x (subset_closure hx) t ⟨ht.1.le,ht.2⟩).le)
    (fun x hx t ht => (hUEq x (subset_closure hx) t ⟨ht.1.le,ht.2⟩).ge)
  exact fun x hx t ht => le_antisymm (hUV x hx t ht) (hVU x hx t ht)

end Yau.Proofs.F05Aux
