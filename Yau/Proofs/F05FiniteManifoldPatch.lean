import Yau.Proofs.F05ManifoldPatch
import Yau.Proofs.F05ManifoldSourcePatch
import Yau.LeafProofs.L16FinitePhysicalParametrix

/-! Actual finite manifold patch sums preserve separate higher and lower
budgets, with the geometric constants preceding every time and function. -/

open Set
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05FiniteManifoldPatch (A : AtlasData M) (β : Fin A.count → M.Carrier → ℝ)
    (v : Fin A.count → Point n → ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  ∑ j,F05ManifoldPatch A j (β j) (v j) x t

theorem F05_finite_manifold_patch_budget {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (β : Fin A.count → M.Carrier → ℝ)
    (hβ : ∀ j, SmoothFn (β j))
    (hSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T K L : ℝ) (v : Fin A.count → Point n → ℝ),
      T ≤ 1 → 0 ≤ K → 0 ≤ L →
      (∀ j, SchauderBound α (cylinder univ 0 T) (v j) K) →
      (∀ j, HolderBound α (cylinder univ 0 T) (fun p => (v j p,spatialD (v j) p)) L) →
      ∀ i : Fin A.count,
        SchauderBound α (F05Q A i T) (pull A i (F05FiniteManifoldPatch A β v)) (C*(K+L)) ∧
        HolderBound α (F05Q A i T)
          (fun p => (pull A i (F05FiniteManifoldPatch A β v) p,
            spatialD (pull A i (F05FiniteManifoldPatch A β v)) p)) (C*L) := by
  classical
  choose B hB hPatch using (fun j : Fin A.count => F05_manifold_patch_budget hA j (hβ j) (hSupport j) hα hα1)
  let C := 1+∑ j,B j
  have hSum : 0 ≤ ∑ j,B j := Finset.sum_nonneg (fun j _ => (hB j).le)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro T K L v hT hK hL hHigh hLow i
  have hEach (j : Fin A.count) := hPatch j T K L (v j) hT (hHigh j) (hLow j) i
  have hS := schauderBound_finset_sum Finset.univ (fun j _ => (hEach j).1)
  have hLower := lowPair_holderBound_finset_sum Finset.univ
    (fun j _ => (hEach j).1.1) (fun j _ => (hEach j).2)
  have hBudget (P : ℝ) (hP : 0 ≤ P) : (∑ j,B j*P) ≤ C*P := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hP
  exact ⟨schauderBound_mono_const hS (hBudget (K+L) (add_nonneg hK hL)),
    holderBound_mono_const hLower (hBudget L hL)⟩

theorem F05_finite_manifold_source_budget {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (β : Fin A.count → M.Carrier → ℝ)
    (hβ : ∀ j, SmoothFn (β j))
    (hSupport : ∀ j, tsupport (β j) ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T F : ℝ) (f : Fin A.count → Point n → ℝ), 0 ≤ F →
      (∀ j, HolderBound α (cylinder (closure (F05ModelOpen A j)) 0 T) (f j) F) →
      ∀ i : Fin A.count, HolderBound α (F05Q A i T) (pull A i (F05FiniteManifoldPatch A β f)) (C*F) := by
  classical
  choose B hB hPatch using (fun j : Fin A.count => F05_manifold_source_patch_budget hA j (hβ j) (hSupport j) hα hα1)
  let C := 1+∑ j,B j
  have hSum : 0 ≤ ∑ j,B j := Finset.sum_nonneg (fun j _ => (hB j).le)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro T F f hF hHolder i
  have hSumHolder := holderBound_finset_sum Finset.univ (fun j _ => hPatch j T F (f j) (hHolder j) i)
  apply holderBound_mono_const hSumHolder
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hF

end Yau.Proofs.F05Aux
