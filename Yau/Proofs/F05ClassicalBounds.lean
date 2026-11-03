import Yau.Proofs.F05ClassicalComparison
import Yau.Proofs.F05ClassicalLaplacian

/-! Compactness and actual C2 continuity supply all value/reaction bounds
in classical comparison; no bound on the unknown is added as a premise. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_classical_comparison {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {T : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T)) (w u : M.Carrier → ℝ → ℝ)
    (hWCont : ContinuousOn (fun q : M.Carrier × ℝ => w q.1 q.2) (closure O ×ˢ Icc 0 T))
    (hUCont : ContinuousOn (fun q : M.Carrier × ℝ => u q.1 q.2) (closure O ×ˢ Icc 0 T))
    (hW : ∀ i, C2 (F05Q A i T) (pull A i w)) (hU : ∀ i, C2 (F05Q A i T) (pull A i u))
    (hInitial : ∀ x ∈ closure O, w x 0 ≤ u x 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t ≤ u x t)
    (hSub : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, derivWithin (w x) (Icc 0 T) t ≤
      scalarNonlinearRHS (scalarCurvature (h t) x) (laplacian (h t) (fun y => w y t) x) (w x t))
    (hSuper : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, scalarNonlinearRHS (scalarCurvature (h t) x)
      (laplacian (h t) (fun y => u y t) x) (u x t) ≤ derivWithin (u x) (Icc 0 T) t) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, w x t ≤ u x t := by
  classical
  obtain ⟨D,hD⟩ := ((F05_atlas_closure_compact hA).prod isCompact_Icc).exists_bound_of_continuousOn hUCont
  let K := 1+|D|
  have hLower (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Ioc 0 T) : -K ≤ u x t := by
    have hh : |u x t| ≤ D := hD (x,t) ⟨subset_closure hx,ht.1.le,ht.2⟩
    dsimp only [K]
    linarith [neg_abs_le (u x t),le_abs_self D]
  have hEach (i : Fin A.count) : ∃ C : ℝ, ∀ q ∈ F05Q A i T,
      |pull A i (fun x t => scalarCurvature (h t) x-laplacian (h t) (fun y => u y t) x) q| ≤ C := by
    have hDSub : F05D A i ⊆ Metric.closedBall 0 2 := fun z hz =>
      by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
    have hCompactD : IsCompact (F05D A i) :=
      (isCompact_closedBall (0 : Space n) 2).of_isClosed_subset (F05D_isClosed A i) hDSub
    have hSubQ : F05Q A i T ⊆ Metric.ball 0 3 ×ˢ Icc 0 T := fun q hq => ⟨F05D_mem_ball hq.1,hq.2⟩
    have hScalar := (F05_pull_spacetime_smooth hA _ hR i).continuousOn.mono hSubQ
    have hLap := F05_pull_laplacian_continuous_C2 hA h u hh i (hU i)
    exact (hCompactD.prod isCompact_Icc).exists_bound_of_continuousOn (hScalar.sub hLap)
  choose C hC using hEach
  let A₀ := 1+∑ i,|C i|
  have hBound (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Ioc 0 T) :
      |scalarCurvature (h t) x-laplacian (h t) (fun y => u y t) x| ≤ A₀ := by
    obtain ⟨i,z,hz,heq⟩ := F05_cover hA (subset_closure hx)
    have hChart := hC i (z,t) ⟨hz,ht.1.le,ht.2⟩
    change |scalarCurvature (h t) (lift A i z)-laplacian (h t) (fun y => u y t) (lift A i z)| ≤ C i at hChart
    rw [heq] at hChart
    have hSum := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => abs_nonneg (C j))
      (Finset.mem_univ i)
    dsimp only [A₀]
    linarith [le_abs_self (C i)]
  exact F05_classical_comparison_bounded hA h hT hh w u hWCont hUCont hW hU K A₀ hLower hBound
    hInitial hBoundary hSub hSuper

end Yau.Proofs.F05Aux
