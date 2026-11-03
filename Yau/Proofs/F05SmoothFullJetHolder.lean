import Yau.Proofs.F05SmoothSchauder
import Yau.Proofs.F05BootstrapSchauderLimit

/-! A fixed smooth datum has a uniform Hölder bound for its complete
native four-jet tuple, including the low value/gradient pair. The budget
precedes every smaller endpoint and every exponent in (0,1). -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_chart_full_jet_holder {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (p : M.Carrier → ℝ → ℝ) {S : ℝ}
    (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S)) (i : Fin A.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α < 1 →
      ∀ T : ℝ, 0 < T → T ≤ S →
      HolderBound α (F05Q A i T)
        (fun z => ((pull A i p z,spatialD (pull A i p) z),
          (spatialDD (pull A i p) z,timeD (F05Q A i T) (pull A i p) z))) C := by
  have hφ := F05_pull_spacetime_smooth hA p hp i
  have hSpatial := F05_joint_spatial_jets_smooth Metric.isOpen_ball hφ
  have hTime := F05_joint_time_derivative_smooth (uniqueDiffOn_Icc hS) hφ
  have hAll := (hφ.prodMk hSpatial.1).prodMk (hSpatial.2.prodMk hTime)
  obtain ⟨C,hC,hBudget⟩ := F05_compact_cylinder_holder Metric.isOpen_ball
    (isCompact_closedBall (0 : Space n) 2) (convex_closedBall (0 : Space n) 2)
    (Metric.closedBall_subset_ball (by norm_num : (2 : ℝ) < 3)) hS hAll
  refine ⟨C,hC,?_⟩
  intro α hα hα1 T hT hTS
  have hSub : F05Q A i T ⊆ cylinder (Metric.closedBall 0 2) 0 T :=
    fun z hz => ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1.1,hz.2⟩
  have hRestricted := holderBound_mono (hBudget α hα hα1 T hTS) hSub
  apply holderBound_congr_on hRestricted
  intro z hz
  refine Prod.ext (Prod.ext rfl rfl) (Prod.ext rfl ?_)
  exact (F05_timeD_smooth_restrict hA hp hT hTS i hz).symm

theorem F05_smooth_full_jet_holder_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (p : M.Carrier → ℝ → ℝ) {S : ℝ}
    (hS : 0 < S) (hp : SmoothSpaceTime p (Icc 0 S)) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α < 1 →
      ∀ T : ℝ, 0 < T → T ≤ S → ∀ i,
      HolderBound α (F05Q A i T)
        (fun z => ((pull A i p z,spatialD (pull A i p) z),
          (spatialDD (pull A i p) z,timeD (F05Q A i T) (pull A i p) z))) C := by
  classical
  choose B hB hBudget using fun i : Fin A.count => F05_smooth_chart_full_jet_holder hA p hS hp i
  let C := 1+∑ i,B i
  have hSum : 0 ≤ ∑ i,B i := Finset.sum_nonneg (fun i _ => (hB i).le)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro α hα hα1 T hT hTS i
  apply holderBound_mono_const (hBudget i α hα hα1 T hT hTS)
  have hSingle := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hB j).le) (Finset.mem_univ i)
  dsimp only [C]
  linarith

end Yau.Proofs.F05Aux
