import Yau.Proofs.F05CrossChartBudget
import Yau.Proofs.F05LocalC2Transfer

/-! A literal supported manifold patch has the full physical chart budgets
and genuine initial and lateral traces. -/

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ManifoldPatch (A : AtlasData M) (j : Fin A.count) (β : M.Carrier → ℝ)
    (v : Point n → ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  β x*v (F05Coord A j x,t)

theorem F05_manifold_patch_budget {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (j : Fin A.count) {β : M.Carrier → ℝ}
    (hβ : SmoothFn β) (hSupport : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T K0 L0 : ℝ) (v : Point n → ℝ), T ≤ 1 →
      SchauderBound α (cylinder univ 0 T) v K0 →
      HolderBound α (cylinder univ 0 T) (fun p => (v p,spatialD v p)) L0 →
      ∀ i : Fin A.count,
        SchauderBound α (F05Q A i T) (pull A i (F05ManifoldPatch A j β v)) (C*(K0+L0)) ∧
        HolderBound α (F05Q A i T)
          (fun p => (pull A i (F05ManifoldPatch A j β v) p,
            spatialD (pull A i (F05ManifoldPatch A j β v)) p)) (C*L0) := by
  classical
  choose C hC hBudget using (fun i : Fin A.count => F05_cross_chart_patch_budget hA i j hβ hSupport hα hα1)
  let C₀ := 1+∑ i,C i
  have hSum : 0 ≤ ∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hCi (i : Fin A.count) : C i ≤ C₀ := by
    have h := Finset.single_le_sum
      (fun k (_ : k ∈ (Finset.univ : Finset (Fin A.count))) => (hC k).le) (Finset.mem_univ i)
    dsimp only [C₀]
    linarith
  refine ⟨C₀,hC₀,?_⟩
  intro T K0 L0 v hT hv hLow i
  obtain ⟨hLocal,hLocalLow⟩ := hBudget i T K0 L0 v hT hv hLow
  have hNear : ∀ x ∈ F05D A i, ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 T,
      F05CrossChartPatch A i j β v (y,t) = pull A i (F05ManifoldPatch A j β v) (y,t) := by
    intro x hx
    exact (F05CrossChartPatch_eq_near A i j β v hx).mono fun y hy t _ => hy t
  have hTransfer := F05_local_schauder_transfer hLocal hLocalLow hNear
  exact ⟨schauderBound_mono_const hTransfer.1
      (mul_le_mul_of_nonneg_right (hCi i) (add_nonneg hv.2.1 hLow.1)),
    holderBound_mono_const hTransfer.2 (mul_le_mul_of_nonneg_right (hCi i) hLow.1)⟩

theorem F05ManifoldPatch_initial (A : AtlasData M) (j : Fin A.count)
    (β : M.Carrier → ℝ) {v : Point n → ℝ} (h0 : ∀ z, v (z,0) = 0)
    (x : M.Carrier) : F05ManifoldPatch A j β v x 0 = 0 := by
  simp only [F05ManifoldPatch,h0,mul_zero]

theorem F05ManifoldPatch_lateral {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (j : Fin A.count) {β : M.Carrier → ℝ}
    (hSupport : tsupport β ⊆ lift A j '' Metric.closedBall 0 (3/4))
    {T : ℝ} {v : Point n → ℝ}
    (hBoundary : ∀ z ∈ frontier (F05ModelOpen A j), ∀ t ∈ Icc 0 T, v (z,t) = 0)
    {x : M.Carrier} (hx : x ∈ frontier O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05ManifoldPatch A j β v x t = 0 := by
  by_cases hβ : β x = 0
  · simp only [F05ManifoldPatch,hβ,zero_mul]
  obtain ⟨z,hz,heq⟩ := hSupport (subset_tsupport β hβ)
  have hn : ‖z‖ ≤ 3/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  have hz3 : z ∈ Metric.ball (0 : Space n) 3 :=
    Metric.closedBall_subset_ball (by norm_num : (3/4 : ℝ) < 3) hz
  obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 j
  have hClosure := (hPhysical z hz3).2.1
  have hFrontier := (hPhysical z hz3).2.2
  rw [heq] at hClosure hFrontier
  have hzD : z ∈ F05D A j := ⟨hn.trans (by norm_num),hClosure.mp (frontier_subset_closure hx)⟩
  have hzB : z ∈ frontier (F05ModelOpen A j) := by
    have hFace := hFrontier.mp hx
    cases hν : A.normal j with
    | none => simp only [hν] at hFace
    | some k =>
      have hzk : realCoord z k = 0 := by simpa only [hν] using hFace
      simpa only [F05ModelOpen,hν,coordinate_halfSpace_frontier,mem_ofPred_eq] using hzk
  unfold F05ManifoldPatch
  rw [← heq,F05Coord_lift hA hzD,hBoundary z hzB t ht,mul_zero]

end Yau.Proofs.F05Aux
