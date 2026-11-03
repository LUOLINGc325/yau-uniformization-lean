import Yau.Proofs.F05CompactDirichletSolution

/-! The actual finite Schauder solution has the original time derivative
at every physical point. Restricting to a later closed slab preserves its
literal nonlinear equation, including both one-sided time faces. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_compact_solution_time_differentiable {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {h : ℝ → HermitianField M} {p w : M.Carrier → ℝ → ℝ}
    {T : ℝ} (hw : F05CompactDirichletSolution O A h p T w)
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    DifferentiableWithinAt ℝ (w x) (Icc 0 T) t := by
  obtain ⟨β,K,hβ,hβ1,hK,hSch,hCont,h0,hBoundary,hEq⟩ := hw
  obtain ⟨i,z,hz,hzx⟩ := F05_cover hA hx
  have hFiber : {a : ℝ | (z,a) ∈ F05Q A i T} = Icc 0 T := by
    ext a
    exact and_iff_right hz
  have hDiff := (hSch i).1.2.2.2.2.2 (z,t) ⟨hz,ht⟩
  simpa only [hFiber,pull,hzx] using hDiff

theorem F05_compact_solution_late_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {h : ℝ → HermitianField M} {p w : M.Carrier → ℝ → ℝ}
    {l T : ℝ} (hl : 0 ≤ l) (hlT : l < T) (hw : F05CompactDirichletSolution O A h p T w) :
    ∀ x ∈ closure O, ∀ t ∈ Icc l T,
      derivWithin (w x) (Icc l T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*scalarCurvature (h t) x := by
  have hSub : Icc l T ⊆ Icc 0 T := fun t ht => ⟨hl.trans ht.1,ht.2⟩
  intro x hx t ht
  have hd := F05_compact_solution_time_differentiable hA hw hx (hSub ht)
  have hTime := (hd.hasDerivWithinAt.mono hSub).derivWithin (uniqueDiffOn_Icc hlT t ht)
  obtain ⟨β,K,hβ,hβ1,hK,hSch,hCont,h0,hBoundary,hEq⟩ := hw
  exact hTime.trans (hEq x hx t (hSub ht))

end Yau.Proofs.F05Aux
