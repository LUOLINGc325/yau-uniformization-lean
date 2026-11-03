import Yau.Proofs.F05FlowPatchSolver
import Yau.Proofs.F05PatchSources

/-! Actual local solvers composed with the genuine source maps have uniform
budgets and the exact original source term. The initial time jet is proved. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05FlowSourcePatchData (A : AtlasData M) (χ : Fin A.count → M.Carrier → ℝ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ) (α T ρ K E : ℝ)
    (U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ) : Prop :=
  ∀ i : Fin A.count,
    (∀ f g p, p ∈ cylinder univ 0 T → U i (f+g) p = U i f p+U i g p) ∧
    (∀ (d : ℝ) f p, p ∈ cylinder univ 0 T → U i (d • f) p = d*U i f p) ∧
    (∀ f x, H i f (x,0) = 0) ∧ ∀ f,
      SchauderBound α (cylinder univ 0 T) (U i f) (K*‖f‖) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (U i f p,spatialD (U i f) p)) (K*‖f‖*ρ^(1-α)) ∧
      (∀ x, U i f (x,0) = 0) ∧
      (∀ x ∈ frontier (F05ModelOpen A i), ∀ t ∈ Icc 0 T, U i f (x,t) = 0) ∧
      (∀ x ∈ closure (F05ModelOpen A i),
        timeD (cylinder (closure (F05ModelOpen A i)) 0 T) (U i f) (x,0) = 0) ∧
      (∀ p ∈ cylinder (closure (F05ModelOpen A i)) 0 T,
        linearOp (cylinder (closure (F05ModelOpen A i)) 0 T)
          (F05PrincipalExtension (F05FlowPrincipal A i h c))
          (F05DriftExtension (F05FlowDrift A i h c)) (U i f) p =
          F05ModelPartition A χ i p.1*holderGraphFun (f.val i) p-H i f p) ∧
      HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T) (H i f) (E*‖f‖*ρ^(1-α))

theorem F05_flow_source_patch_solvers {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ δ K E : ℝ, 0 < δ ∧ δ ≤ S ∧ δ ≤ 1 ∧ 0 < K ∧ 0 < E ∧
      ∀ (ρ T : ℝ), 0 < ρ → ρ ≤ 1 → 0 < T → T ≤ δ → T ≤ ρ^2 →
        ∃ U H : Fin A.count → F05SourceZeroGraph A α T → Point n → ℝ,
          F05FlowSourcePatchData A χ h c α T ρ K E U H := by
  classical
  obtain ⟨δ,K,E,hδ,hδS,hδ1,hK,hE,hSolvers⟩ := F05_flow_patch_solvers hA hχ h c hS hh hc hPos hα hα1
  obtain ⟨B,hB,hSources⟩ := F05_patch_source_map A hα hα1
  refine ⟨δ,K*B,E*B,hδ,hδS,hδ1,mul_pos hK hB,mul_pos hE hB,?_⟩
  intro ρ T hρ hρ1 hT hTδ hTρ
  choose W H hData using (hSolvers ρ T hρ hρ1 hT hTδ hTρ)
  choose P hP hP0 hPeq using (hSources T hT)
  let U (i : Fin A.count) (f : F05SourceZeroGraph A α T) := W i (P i f)
  let V (i : Fin A.count) (f : F05SourceZeroGraph A α T) := H i (P i f)
  refine ⟨U,V,?_⟩
  intro i
  obtain ⟨hAdd,hSmul,hH0,hWH⟩ := hData i
  refine ⟨?_,?_,fun f x => hH0 (P i f) x,?_⟩
  · intro f g p hp
    dsimp only [U]
    rw [map_add]
    exact hAdd _ _ p hp
  · intro d f p hp
    dsimp only [U]
    rw [map_smul]
    exact hSmul d _ p hp
  · intro f
    obtain ⟨⟨hHigh,hLow,hW0,hWB,hEq⟩,hHHolder,hOriginal⟩ := hWH (P i f)
    have hNorm : ‖P i f‖ ≤ B*‖f‖ :=
      ((P i).le_opNorm f).trans (mul_le_mul_of_nonneg_right (hP i) (norm_nonneg _))
    have hKBudget : K*‖P i f‖ ≤ (K*B)*‖f‖ := by
      calc
        _ ≤ K*(B*‖f‖) := mul_le_mul_of_nonneg_left hNorm hK.le
        _ = _ := by ring
    have hEBudget : E*‖P i f‖ ≤ (E*B)*‖f‖ := by
      calc
        _ ≤ E*(B*‖f‖) := mul_le_mul_of_nonneg_left hNorm hE.le
        _ = _ := by ring
    have hPower : 0 ≤ ρ^(1-α) := Real.rpow_nonneg hρ.le _
    refine ⟨schauderBound_mono_const hHigh hKBudget,
      holderBound_mono_const hLow (mul_le_mul_of_nonneg_right hKBudget hPower),hW0,hWB,?_,?_,
      holderBound_mono_const hHHolder (mul_le_mul_of_nonneg_right hEBudget hPower)⟩
    · intro x hx
      have hZero := F05_patch_initial_time_zero (F05ModelOpen A i) T hT.le
        (F05PrincipalExtension (F05FlowPrincipal A i h c)) (F05DriftExtension (F05FlowDrift A i h c))
        (W i (P i f)) (compatibleHolderFun (P i f)) (H i (P i f)) (F05ModelPartition A χ i)
        hW0 (hP0 i f) (hH0 (P i f)) hEq x hx
      have hFiber : {t : ℝ | (x,t) ∈ cylinder (closure (F05ModelOpen A i)) 0 T} = Icc 0 T := by
        ext t
        change (x ∈ closure (F05ModelOpen A i) ∧ t ∈ Icc 0 T) ↔ t ∈ Icc 0 T
        exact and_iff_right hx
      unfold timeD
      rw [hFiber]
      exact hZero
    · intro p hp
      have hReplace : F05ModelPartition A χ i p.1*compatibleHolderFun (P i f) p =
          F05ModelPartition A χ i p.1*holderGraphFun (f.val i) p := by
        by_cases hψ : F05ModelPartition A χ i p.1 = 0
        · rw [hψ,zero_mul,zero_mul]
        have hBall := F05ModelPartition_tsupport hA hχ i (subset_tsupport (F05ModelPartition A χ i) hψ)
        have hn : ‖p.1‖ ≤ 1/4 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hBall
        have hFace := hp.1
        rw [F05ModelOpen_eq,F05FlatOpen_closure] at hFace
        have hpQ : p ∈ F05Q A i T := ⟨⟨hn.trans (by norm_num),hFace⟩,hp.2⟩
        rw [hPeq i f p hpQ (hn.trans (by norm_num))]
      exact (hEq p hp).trans (by rw [hReplace])

end Yau.Proofs.F05Aux
