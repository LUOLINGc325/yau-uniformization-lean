import Yau.Proofs.F05FlattenedSmooth
import Yau.Proofs.F05CompactHolder

/-! Actual smooth scalar multiples of the actual flow coefficients have
uniform Holder budgets before the moving endpoint and every source. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_pull_spacetime_smooth {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (c : M.Carrier → ℝ → ℝ) {I : Set ℝ}
    (hc : SmoothSpaceTime c I) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (pull A i c) (Metric.ball 0 3 ×ˢ I) := by
  have hInverse : ContDiffOn ℝ ∞ (fun p : Point n => (A.inverse i p.1,p.2)) (Metric.ball 0 3 ×ˢ I) :=
    (((hA.1 i).2.2.2.1).comp contDiffOn_fst (fun p hp => hp.1)).prodMk contDiffOn_snd
  have hMap (p : Point n) (hp : p ∈ Metric.ball 0 3 ×ˢ I) :
      (A.inverse i p.1,p.2) ∈ chartTarget (A.center i) ×ˢ I :=
    ⟨(hA.1 i).2.1 ((hA.1 i).2.2.2.2.1 ⟨p.1,hp.1,rfl⟩),hp.2⟩
  exact (hc (A.center i)).comp hInverse hMap

theorem F05_linear_coefficients_smooth {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {I : Set ℝ} (hh : MetricFamilySmooth h I) (hc : SmoothSpaceTime c I) (i : Fin A.count) :
    SmoothCoefficients (Metric.ball 0 3 ×ˢ I)
      (fun p => pull A i c p • flatA (h p.2) A i p)
      (fun p j => pull A i c p * flatB (h p.2) A i p j) := by
  have hScalar := F05_pull_spacetime_smooth hA c hc i
  have hMetric := F05_flat_coefficients_smooth hA h hh i
  exact ⟨hScalar.smul hMetric.1,fun j => hScalar.mul (hMetric.2 j)⟩

theorem F05_linear_coefficients_holder {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (i : Fin A.count) :
    ∃ B : ℝ, 0 < B ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ), T ≤ S →
      HolderBound α (cylinder (Metric.closedBall 0 2) 0 T)
        (fun p => pull A i c p • flatA (h p.2) A i p) B ∧
      ∀ j, HolderBound α (cylinder (Metric.closedBall 0 2) 0 T)
        (fun p => pull A i c p * flatB (h p.2) A i p j) B := by
  classical
  have hSmooth := F05_linear_coefficients_smooth hA h c hh hc i
  have hKU : Metric.closedBall (0 : Space n) 2 ⊆ Metric.ball 0 3 :=
    Metric.closedBall_subset_ball (by norm_num)
  obtain ⟨C,hC,hPrincipal⟩ := F05_compact_cylinder_holder Metric.isOpen_ball
    (isCompact_closedBall (0 : Space n) 2) (convex_closedBall (0 : Space n) 2) hKU hS hSmooth.1
  have hDrift (j : RIdx n) := F05_compact_cylinder_holder Metric.isOpen_ball
    (isCompact_closedBall (0 : Space n) 2) (convex_closedBall (0 : Space n) 2) hKU hS (hSmooth.2 j)
  choose D hD hDrift using hDrift
  let B := 1+C+∑ j,D j
  have hSum : 0 ≤ ∑ j,D j := Finset.sum_nonneg (fun j _ => (hD j).le)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hCB : C ≤ B := by dsimp only [B]; linarith
  have hDB (j : RIdx n) : D j ≤ B := by
    have h := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (RIdx n))) => (hD k).le)
      (Finset.mem_univ j)
    dsimp only [B]
    linarith
  refine ⟨B,hB,?_⟩
  intro α hα hα1 T hTS
  exact ⟨holderBound_mono_const (hPrincipal α hα hα1 T hTS) hCB,
    fun j => holderBound_mono_const (hDrift j α hα hα1 T hTS) (hDB j)⟩

end Yau.Proofs.F05Aux
