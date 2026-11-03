import Yau.Proofs.F05CompactDirichletSolution
import Yau.Proofs.F05ManifoldPasteContinuity
import Yau.Proofs.F05HolderExponentLowering

/-! An actual late closed-slab solution pastes to the earlier compact
solution. Different original finite Hölder exponents are reduced to their
positive minimum; positive-time smoothness is subsequently bootstrapped
from the resulting original compact solution, rather than assumed. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_compact_solution_of_late_solution {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p u W : M.Carrier → ℝ → ℝ)
    {r t₀ T α L : ℝ} (hr : 0 < r) (hrt₀ : r ≤ t₀) (hrT : r < T)
    (hu : F05CompactDirichletSolution O A h p t₀ u)
    (hα : 0 < α) (hL : 0 < L)
    (hWSch : ∀ i, SchauderBound α (cylinder (F05D A i) r T) (pull A i W) L)
    (hWCont : ContinuousOn (fun z : M.Carrier × ℝ => W z.1 z.2) (closure O ×ˢ Icc r T))
    (hWBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc r T, W x t = p x t)
    (hWEq : ∀ x ∈ closure O, ∀ t ∈ Icc r T,
      derivWithin (W x) (Icc r T) t = Real.exp (-W x t)*laplacian (h t) (fun y => W y t) x+
        (1-Real.exp (-W x t))*scalarCurvature (h t) x)
    (hTrace : ∀ x ∈ closure O, u x r = W x r) :
    ∃ v : M.Carrier → ℝ → ℝ, F05CompactDirichletSolution O A h p T v ∧
      ∀ x ∈ closure O, ∀ t ∈ Icc 0 r, v x t = u x t := by
  have hEarly := F05_compact_solution_restrict hA h p u hr hrt₀ hu
  obtain ⟨β,C,hβ,hβ1,hC,hUSch,hUCont,hU0,hUBoundary,hUEq⟩ := hEarly
  let η := min β α
  have hη : 0 < η := lt_min hβ hα
  have hη1 : η < 1 := (min_le_left β α).trans_lt hβ1
  have hUSmall (i : Fin A.count) : SchauderBound η (F05Q A i r) (pull A i u) (2*C) :=
    F05_schauder_lower_exponent hη.le (min_le_left β α) (hUSch i)
  have hWSmall (i : Fin A.count) :
      SchauderBound η (cylinder (F05D A i) r T) (pull A i W) (2*L) :=
    F05_schauder_lower_exponent hη.le (min_le_right β α) (hWSch i)
  have hPaste := F05_manifold_nonlinear_paste hA h hr hrT hη u W hUSmall hWSmall hTrace hUEq hWEq
  have hCont := F05_manifold_timePaste_continuous hr.le hrT.le u W hUCont hWCont hTrace
  let v := F05ManifoldTimePaste r u W
  have hv : F05CompactDirichletSolution O A h p T v := by
    refine ⟨η,2*(2*C+2*L),hη,hη1,by positivity,hPaste.1,hCont,?_,?_,hPaste.2⟩
    · intro x hx
      simpa only [v,F05ManifoldTimePaste,hr.le,ite_true] using hU0 x hx
    · intro x hx t ht
      by_cases htr : t ≤ r
      · simpa only [v,F05ManifoldTimePaste,htr,ite_true] using hUBoundary x hx t ⟨ht.1,htr⟩
      · simpa only [v,F05ManifoldTimePaste,htr,ite_false] using
          hWBoundary x hx t ⟨(not_le.mp htr).le,ht.2⟩
  refine ⟨v,hv,?_⟩
  intro x hx t ht
  simp only [v,F05ManifoldTimePaste,ht.2,ite_true]

end Yau.Proofs.F05Aux
