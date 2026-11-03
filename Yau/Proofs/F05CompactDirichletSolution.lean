import Yau.Proofs.F05SmoothDirichletLocal
import Yau.Proofs.F05ClassicalRestriction

/-! The actual compact-domain solution property used in continuation.
It records the literal finite Schauder norm and original nonlinear PDE;
positive-time smoothness is derived from the proved bootstrap. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05CompactDirichletSolution (O : Set M.Carrier) (A : AtlasData M)
    (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ) (T : ℝ)
    (w : M.Carrier → ℝ → ℝ) : Prop :=
  ∃ β K : ℝ, 0 < β ∧ β < 1 ∧ 0 < K ∧
    (∀ i, SchauderBound β (F05Q A i T) (pull A i w) K) ∧
    ContinuousOn (fun z : M.Carrier × ℝ => w z.1 z.2) (closure O ×ˢ Icc 0 T) ∧
    (∀ x ∈ closure O, w x 0 = p x 0) ∧
    (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = p x t) ∧
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*scalarCurvature (h t) x

theorem F05_compact_dirichlet_local {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ) {S : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S)) (hp : SmoothSpaceTime p (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (hCompat : ∀ x, derivWithin (p x) (Icc 0 S) 0 =
      Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧ ∀ T : ℝ, 0 < T → T ≤ δ →
      ∃ w : M.Carrier → ℝ → ℝ, F05CompactDirichletSolution O A h p T w := by
  obtain ⟨δ,K,hδ,hδS,hδ1,hK,hSolve⟩ := F05_schauder_nonlinear_local_general hA hχ h p hS hh hp hR
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1) hCompat
  refine ⟨δ,hδ,hδS,?_⟩
  intro T hT hTδ
  obtain ⟨w,hSch,hCont,hInit,hBoundary,hEq⟩ := hSolve T hT hTδ
  exact ⟨w,1/2,K,by norm_num,by norm_num,hK,hSch,hCont,hInit,hBoundary,hEq⟩

theorem F05_compact_solution_positive_smooth (hn : 0 < n) {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p w : M.Carrier → ℝ → ℝ)
    {T : ℝ} (hT : 0 < T) (hh : MetricFamilySmooth h (Icc 0 T))
    (hp : SmoothSpaceTime p (Icc 0 T))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T))
    (hw : F05CompactDirichletSolution O A h p T w) :
    ∀ s : ℝ, 0 < s → s < T → ∀ i,
      ContDiffOn ℝ ∞ (pull A i w) (F05D A i ×ˢ Icc s T) := by
  obtain ⟨β,K,hβ,hβ1,hK,hSch,hCont,hInit,hBoundary,hEq⟩ := hw
  exact F05_positive_time_boundary_bootstrap hn hA h _ p w hT hβ hβ1 hh hR hp
    hCont hSch hInit hBoundary hEq

theorem F05_compact_solution_coherent {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p u v : M.Carrier → ℝ → ℝ)
    {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (hU : F05CompactDirichletSolution O A h p S u)
    (hV : F05CompactDirichletSolution O A h p T v) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, u x t = v x t := by
  obtain ⟨β,K,hβ,hβ1,hK,hUSch,hUCont,hU0,hUBoundary,hUEq⟩ := hU
  obtain ⟨γ,L,hγ,hγ1,hL,hVSch,hVCont,hV0,hVBoundary,hVEq⟩ := hV
  exact F05_classical_solution_coherent hA h hT hTS hh hR u v hUCont hVCont
    (fun i => (hUSch i).1) (fun i => (hVSch i).1)
    (fun x hx => (hU0 x hx).trans (hV0 x hx).symm)
    (fun x hx t ht => (hUBoundary x hx t ⟨ht.1,ht.2.trans hTS⟩).trans (hVBoundary x hx t ht).symm)
    hUEq hVEq

theorem F05_compact_solution_restrict {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p w : M.Carrier → ℝ → ℝ)
    {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S)
    (hw : F05CompactDirichletSolution O A h p S w) :
    F05CompactDirichletSolution O A h p T w := by
  obtain ⟨β,K,hβ,hβ1,hK,hSch,hCont,h0,hBoundary,hEq⟩ := hw
  have hSub : Icc (0 : ℝ) T ⊆ Icc 0 S := Icc_subset_Icc le_rfl hTS
  exact ⟨β,K,hβ,hβ1,hK,fun i => F05_schauder_restrict_interval hT le_rfl hTS (hSch i),
    hCont.mono (prod_mono subset_rfl hSub),h0,
    fun x hx t ht => hBoundary x hx t (hSub ht),
    F05_nonlinear_solution_restrict hA h hT hTS w (fun i => (hSch i).1) hEq⟩

end Yau.Proofs.F05Aux
