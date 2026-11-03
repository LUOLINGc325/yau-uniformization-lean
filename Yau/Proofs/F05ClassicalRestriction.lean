import Yau.Proofs.F05ClassicalUniqueness
import Yau.Proofs.F05BootstrapRestrictions
import Yau.Proofs.F05SmoothSlices

/-! The original one-sided nonlinear equation restricts to every shorter
closed slab, including its initial and terminal faces. Native uniqueness
then makes all actual local solutions with the same data coherent. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_nonlinear_solution_restrict {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S)
    (w : M.Carrier → ℝ → ℝ) (hw : ∀ i, C2 (F05Q A i S) (pull A i w))
    (hEquation : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S,
      derivWithin (w x) (Icc 0 S) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*scalarCurvature (h t) x) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*scalarCurvature (h t) x := by
  intro x hx t ht
  obtain ⟨i,y,hy,hyx⟩ := F05_cover hA hx
  have hFiber : {r : ℝ | (y,r) ∈ F05Q A i S} = Icc 0 S := by
    ext r
    simp only [F05Q,cylinder,mem_prod,hy,true_and,mem_ofPred_eq]
  have hDiff : DifferentiableWithinAt ℝ (w x) (Icc 0 S) t := by
    have hAt := (hw i).2.2.2.2.2 (y,t) ⟨hy,ht.1,ht.2.trans hTS⟩
    simpa only [hFiber,pull,hyx] using hAt
  rw [derivWithin_subset (Icc_subset_Icc le_rfl hTS) (uniqueDiffOn_Icc hT t ht) hDiff]
  exact hEquation x hx t ⟨ht.1,ht.2.trans hTS⟩

theorem F05_classical_solution_coherent {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {T S : ℝ} (hT : 0 < T) (hTS : T ≤ S)
    (hh : MetricFamilySmooth h (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (u v : M.Carrier → ℝ → ℝ)
    (hUCont : ContinuousOn (fun z : M.Carrier × ℝ => u z.1 z.2) (closure O ×ˢ Icc 0 S))
    (hVCont : ContinuousOn (fun z : M.Carrier × ℝ => v z.1 z.2) (closure O ×ˢ Icc 0 T))
    (hU : ∀ i, C2 (F05Q A i S) (pull A i u)) (hV : ∀ i, C2 (F05Q A i T) (pull A i v))
    (hInitial : ∀ x ∈ closure O, u x 0 = v x 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, u x t = v x t)
    (hUEq : ∀ x ∈ closure O, ∀ t ∈ Icc 0 S,
      derivWithin (u x) (Icc 0 S) t = Real.exp (-u x t)*laplacian (h t) (fun y => u y t) x+
        (1-Real.exp (-u x t))*scalarCurvature (h t) x)
    (hVEq : ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (v x) (Icc 0 T) t = Real.exp (-v x t)*laplacian (h t) (fun y => v y t) x+
        (1-Real.exp (-v x t))*scalarCurvature (h t) x) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, u x t = v x t := by
  have hSub : Icc (0 : ℝ) T ⊆ Icc 0 S := fun t ht => ⟨ht.1,ht.2.trans hTS⟩
  have hhT : MetricFamilySmooth h (Icc 0 T) := fun x j k => (hh x j k).mono (prod_mono subset_rfl hSub)
  have hRT : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T) :=
    fun x => (hR x).mono (prod_mono subset_rfl hSub)
  exact F05_classical_solution_unique hA h hT hhT hRT u v
    (hUCont.mono (prod_mono subset_rfl hSub)) hVCont
    (fun i => F05_c2_restrict_interval hT le_rfl hTS (hU i)) hV hInitial hBoundary
    (F05_nonlinear_solution_restrict hA h hT hTS u hU hUEq) hVEq

end Yau.Proofs.F05Aux
