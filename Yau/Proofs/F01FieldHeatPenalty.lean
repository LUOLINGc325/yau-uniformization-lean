import Yau.Proofs.F01SpaceTimeChart
import Yau.Proofs.F01ClosedTimeSlices
import Yau.Proofs.F01LaplacianLinearity
import Yau.Proofs.F01HeatChartNaturality

/-! Actual scalar time slices and the exact native heat operator of a
spatial properness penalty and a strictly increasing linear time penalty. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_time_slice {F : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hF : SmoothSpaceTime F I) (x : M.Carrier) : ContDiffOn ℝ ∞ (F x) I := by
  have hc := (hF x).comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun s hs => ⟨mem_extChartAt_target x, hs⟩)
  apply hc.congr
  intro s hs
  exact (congrArg (fun y => F y s) ((extChartAt (ComplexModel n) x).left_inv
    (mem_extChartAt_source x))).symm

theorem smoothSpaceTime_space_time_penalty {F : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hF : SmoothSpaceTime F I) {f : M.Carrier → ℝ} (hf : SmoothFn f) (δ ε : ℝ) :
    SmoothSpaceTime (fun x t => F x t - δ * f x - ε * t) I := by
  intro a
  exact ((hF a).sub (contDiffOn_const.mul ((hf a).comp contDiffOn_fst (fun p hp => hp.1)))).sub
    (contDiffOn_const.mul contDiffOn_snd)

theorem fieldHeatWithin_sub_space_time_penalty
    (h : ℝ → HermitianField M) {F : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hF : SmoothSpaceTime F I) {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (δ ε : ℝ) (x : M.Carrier) {t : ℝ} (ht : t ∈ I) (hUnique : UniqueDiffWithinAt ℝ I t) :
    fieldHeatWithin h I (fun s y => F y s - δ * f y - ε * s) x t =
      fieldHeatWithin h I (fun s y => F y s) x t + δ * laplacian (h t) f x - ε := by
  have htime := (smoothSpaceTime_time_slice hF x t ht).differentiableWithinAt (by simp)
  have hε : HasDerivWithinAt (fun s : ℝ => ε * s) ε I t := by
    convert ((hasDerivAt_id t).const_mul ε).hasDerivWithinAt using 1 <;> first | rfl | simp
  have htimeP := ((htime.hasDerivWithinAt.sub_const (δ * f x)).sub hε).derivWithin hUnique
  change derivWithin (fun s => F x s - δ * f x - ε * s) I t =
    derivWithin (F x) I t - ε at htimeP
  have hspace := smoothSpaceTime_slice hF ht
  have hδf : SmoothFn (fun y => δ * f y) := fun a => contDiffOn_const.mul (hf a)
  have hsub : SmoothFn (fun y => F y t - δ * f y) := fun a => (hspace a).sub (hδf a)
  have hconst : SmoothFn (fun _ : M.Carrier => ε * t) := fun _ => contDiffOn_const
  unfold fieldHeatWithin
  rw [htimeP, laplacian_sub_native (h t) hsub hconst, laplacian_const_native,
    laplacian_sub_native (h t) hspace hδf, laplacian_const_mul_native (h t) hf δ]
  ring

end Yau.NodeProofs.F01Aux
