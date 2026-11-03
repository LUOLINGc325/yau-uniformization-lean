import Yau.Proofs.F05ClassicalLaplacian
import Yau.Proofs.F05AtlasCompactness

/-! Actual closed-chart C2 data have a finite reaction-value Lipschitz
coefficient on the original compact manifold domain. -/

open Set
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_compact_reaction_bound {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {T : ℝ}
    (hh : MetricFamilySmooth h (Icc 0 T))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T))
    (u : M.Carrier → ℝ → ℝ) (hU : ∀ i, C2 (F05Q A i T) (pull A i u)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      |scalarCurvature (h t) x-laplacian (h t) (fun y => u y t) x| ≤ B := by
  classical
  have hEach (i : Fin A.count) : ∃ C : ℝ, ∀ q ∈ F05Q A i T,
      |pull A i (fun x t => scalarCurvature (h t) x-laplacian (h t) (fun y => u y t) x) q| ≤ C := by
    have hDSub : F05D A i ⊆ Metric.closedBall 0 2 := fun z hz =>
      by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
    have hCompactD : IsCompact (F05D A i) :=
      (isCompact_closedBall (0 : Space n) 2).of_isClosed_subset (F05D_isClosed A i) hDSub
    have hSubQ : F05Q A i T ⊆ Metric.ball 0 3 ×ˢ Icc 0 T := fun q hq => ⟨F05D_mem_ball hq.1,hq.2⟩
    have hScalar := (F05_pull_spacetime_smooth hA _ hR i).continuousOn.mono hSubQ
    exact (hCompactD.prod isCompact_Icc).exists_bound_of_continuousOn
      (hScalar.sub (F05_pull_laplacian_continuous_C2 hA h u hh i (hU i)))
  choose C hC using hEach
  let B := 1+∑ i,|C i|
  have hSum : 0 ≤ ∑ i,|C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨B,by dsimp only [B]; positivity,?_⟩
  intro x hx t ht
  obtain ⟨i,z,hz,heq⟩ := F05_cover hA hx
  have hAt := hC i (z,t) ⟨hz,ht⟩
  change |scalarCurvature (h t) (lift A i z)-laplacian (h t) (fun y => u y t) (lift A i z)| ≤ C i at hAt
  rw [heq] at hAt
  have hSingle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => abs_nonneg (C j))
    (Finset.mem_univ i)
  dsimp only [B]
  linarith [le_abs_self (C i)]

end Yau.Proofs.F05Aux
