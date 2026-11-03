import Yau.Proofs.F05FixedProfileOperator
import Yau.Proofs.F05PhysicalTraceJets
import Yau.Proofs.F05SmoothSlices
import Yau.Proofs.F05CanonicalRegularity

/-! An extension equal to the actual terminal profile on the genuine
physical closure has the same actual Laplacian, including at the physical
boundary. The original equation therefore supplies the restart corner jet. -/

open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_terminal_profile_laplacian {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : HermitianField M) {τ T : ℝ} (hτ : τ ∈ Icc 0 T)
    (w : M.Carrier → ℝ → ℝ) (hw : ∀ i, C2 (F05Q A i T) (pull A i w))
    {g : M.Carrier → ℝ} (hg : SmoothFn g) (hEq : EqOn g (fun x => w x τ) (closure O)) :
    ∀ x ∈ closure O, laplacian h g x = laplacian h (fun y => w y τ) x := by
  intro x hx
  obtain ⟨i,z,hz,hzx⟩ := F05_cover hA hx
  have hG (y : Space n) (hy : y ∈ F05D A i) :
      ContDiffAt ℝ 2 (fun y => g (lift A i y)) y :=
    ((F05_smooth_function_pull_contDiffOn hA i g hg).contDiffAt
      (Metric.isOpen_ball.mem_nhds (F05D_mem_ball hy))).of_le (by simp)
  have hW (y : Space n) (hy : y ∈ F05D A i) :
      ContDiffAt ℝ 2 (fun y => w (lift A i y) τ) y :=
    (hw i).2.2.2.2.1 (y,τ) ⟨hy,hτ⟩
  have hJets := F05_physical_trace_spatial_jets
    (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 2))
    (pull A i (fun x _ => g x)) (pull A i w) τ hG hW
    (fun y hy => hEq (F05D_lift_mem_closure hA hy)) z hz
  rw [← hzx,F05_flattened_laplacian_C2 hA h i g (F05D_mem_ball hz) (hG z hz),
    F05_flattened_laplacian_C2 hA h i (fun y => w y τ) (F05D_mem_ball hz) (hW z hz)]
  simp only [spatialD,spatialDD,pull] at hJets
  rw [hJets.1,hJets.2]

theorem F05_terminal_profile_boundary_jet {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {τ S : ℝ}
    (hτ : 0 < τ) (hτS : τ < S) (p w : M.Carrier → ℝ → ℝ)
    (hp : SmoothSpaceTime p (Icc 0 S))
    (hw : ∀ i, C2 (F05Q A i τ) (pull A i w))
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 τ, w x t = p x t)
    (hEquation : ∀ x ∈ closure O,
      derivWithin (w x) (Icc 0 τ) τ = Real.exp (-w x τ)*laplacian (h τ) (fun y => w y τ) x+
        (1-Real.exp (-w x τ))*scalarCurvature (h τ) x)
    {g : M.Carrier → ℝ} (hg : SmoothFn g) (hEq : EqOn g (fun x => w x τ) (closure O)) :
    EqOn (F05ProfileNonlinearJet h τ g) (fun x => derivWithin (p x) (Icc τ S) τ) (frontier O) := by
  intro x hx
  have hxC := frontier_subset_closure hx
  have hDiff := (F05_smooth_time_slice hp x).differentiableOn (by simp) τ ⟨hτ.le,hτS.le⟩
  have hPast := derivWithin_subset (Icc_subset_Icc le_rfl hτS.le)
    (uniqueDiffOn_Icc hτ τ ⟨hτ.le,le_rfl⟩) hDiff
  have hFuture := derivWithin_subset (Icc_subset_Icc hτ.le le_rfl)
    (uniqueDiffOn_Icc hτS τ ⟨le_rfl,hτS.le⟩) hDiff
  have hTime : derivWithin (w x) (Icc 0 τ) τ = derivWithin (p x) (Icc 0 τ) τ :=
    derivWithin_congr (hBoundary x hx) (hBoundary x hx τ ⟨hτ.le,le_rfl⟩)
  rw [F05ProfileNonlinearJet,hEq hxC,
    F05_terminal_profile_laplacian hA (h τ) ⟨hτ.le,le_rfl⟩ w hw hg hEq x hxC]
  rw [← hEquation x hxC,hTime,hPast]
  exact hFuture.symm

end Yau.Proofs.F05Aux
