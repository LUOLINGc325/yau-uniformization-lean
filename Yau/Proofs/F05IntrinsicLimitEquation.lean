import Yau.Proofs.F05ExhaustionLimitEquation
import Yau.Proofs.F05SmoothNearSpaceTime

/-! The actual full-chart relative equation of the smooth exhaustion
limit is the original intrinsic nonlinear PDE with its ordinary time
derivative at every strictly positive time below the original horizon. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_exhaustion_limit_intrinsic_equation (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (A : ℕ → AtlasData M) (hA : ∀ j, GenuineAtlas (O j) (A j))
    (h : ℝ → HermitianField M) {T : ℝ} (W : M.Carrier → ℝ → ℝ)
    (hSmooth : SmoothSpaceTime W (Ioo 0 T))
    (hEquation : ∀ j (i : Fin (A j).count) m,
      F05RelativeNonlinearEquation none (9/4) (F05ExhaustionTime T m) T
        (fun q => flatA (h q.2) (A j) i q) (fun q a => flatB (h q.2) (A j) i q a)
        (pull (A j) i (fun x t => scalarCurvature (h t) x)) (pull (A j) i W)) :
    ∀ x t, t ∈ Ioo 0 T → deriv (W x) t = Real.exp (-W x t)*laplacian (h t) (fun y => W y t) x+
      (1-Real.exp (-W x t))*scalarCurvature (h t) x := by
  intro x t ht
  have hxAll : x ∈ ⋃ j, O j := by rw [hO.2.2]; exact mem_univ x
  obtain ⟨j,hxj⟩ := mem_iUnion.mp hxAll
  obtain ⟨i,z,hz,hLift⟩ := mem_iUnion.mp ((hA j).2.1 (subset_closure hxj))
  have hz3 : z ∈ Metric.ball (0 : Space n) 3 := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hz.1]
  obtain ⟨m,hm⟩ := F05_exhaustion_time_cover T ht.1
  let l := F05ExhaustionTime T m
  let Q := region (n := n) none (9/4)
  have hzQ : z ∈ Q := ⟨by linarith [hz.1],trivial⟩
  have hX : UniqueDiffOn ℝ Q := F05_region_uniqueDiffOn none (by norm_num)
  have hRaw := F05_pull_spacetime_smooth (hA j) W hSmooth i
  have hSlice : ContDiffOn ℝ ∞ (fun y => pull (A j) i W (y,t)) (Metric.ball 0 3) :=
    hRaw.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy => ⟨hy,ht⟩)
  have hSpatial (y : Space n) (hy : y ∈ Q) :
      ContDiffAt ℝ 2 (fun a => pull (A j) i W (a,t)) y := by
    have hy3 : y ∈ Metric.ball (0 : Space n) 3 := by
      rw [Metric.mem_ball,dist_zero_right]
      linarith [hy.1]
    exact (hSlice.contDiffAt (Metric.isOpen_ball.mem_nhds hy3)).of_le (by simp)
  have hLap := F05_flattened_laplacian_C2 (hA j) (h t) i (fun y => W y t) hz3 (hSpatial z hzQ)
  change laplacian (h t) (fun y => W y t) (lift (A j) i z) =
    (∑ a,∑ b,flatA (h t) (A j) i (z,t) a b*spatialDD (pull (A j) i W) (z,t) (realVec a) (realVec b))+
      ∑ a,flatB (h t) (A j) i (z,t) a*spatialD (pull (A j) i W) (z,t) (realVec a) at hLap
  have hTime : F05RelT (Icc l T) (pull (A j) i W) (z,t) = deriv (W (lift (A j) i z)) t := by
    change derivWithin (W (lift (A j) i z)) (Icc l T) t = deriv (W (lift (A j) i z)) t
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hm ht.2)
  have hEq := hEquation j i m (z,t) ⟨hzQ,hm.le,ht.2.le⟩
  rw [F05RelD_eq_spatialD (v := pull (A j) i W) (z := (z,t))
      (hX z hzQ) ((hSpatial z hzQ).differentiableAt (by norm_num)),
    F05RelDD_eq_spatialDD (v := pull (A j) i W) (z := (z,t)) hX hzQ hSpatial,hTime,← hLap] at hEq
  change deriv (W (lift (A j) i z)) t = Real.exp (-W (lift (A j) i z) t)*
    laplacian (h t) (fun y => W y t) (lift (A j) i z)+
      (1-Real.exp (-W (lift (A j) i z) t))*scalarCurvature (h t) (lift (A j) i z) at hEq
  rwa [hLift] at hEq

end Yau.Proofs.F05Aux
