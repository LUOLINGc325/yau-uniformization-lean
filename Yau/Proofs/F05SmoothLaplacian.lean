import Yau.Proofs.F05SmoothSpatialJets
import Yau.Proofs.F05SmoothC2
import Yau.Proofs.F05LinearCoefficients
import Yau.Proofs.F05FlattenedLaplacian

/-! Smooth actual background data supply both the literal C2 hypothesis and
smooth actual Laplacian in every original physical chart, up to time zero. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_actual_chart_c2 {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {p : M.Carrier → ℝ → ℝ} {S T : ℝ}
    (hp : SmoothSpaceTime p (Icc 0 S)) (hT : 0 < T) (hTS : T ≤ S) (i : Fin A.count) :
    C2 (F05Q A i T) (pull A i p) :=
  F05_smooth_cylinder_c2 Metric.isOpen_ball (fun _ hz => F05D_mem_ball hz) hT hTS
    (F05_pull_spacetime_smooth hA p hp i)

theorem F05_pull_laplacian_smooth {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ)
    {I : Set ℝ} (hh : MetricFamilySmooth h I) (hp : SmoothSpaceTime p I) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (pull A i (fun x t => laplacian (h t) (fun y => p y t) x))
      (Metric.ball 0 3 ×ˢ I) := by
  let Q : Set (Point n) := Metric.ball 0 3 ×ˢ I
  have hφ := F05_pull_spacetime_smooth hA p hp i
  have hJets := F05_joint_spatial_jets_smooth Metric.isOpen_ball hφ
  have hCoeff := F05_flat_coefficients_smooth hA h hh i
  have hD (a : RIdx n) : ContDiffOn ℝ ∞ (fun q => spatialD (pull A i p) q (realVec a)) Q :=
    hJets.1.clm_apply contDiffOn_const
  have hDD (a b : RIdx n) : ContDiffOn ℝ ∞ (fun q => spatialDD (pull A i p) q (realVec a) (realVec b)) Q :=
    (hJets.2.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hExpr : ContDiffOn ℝ ∞ (fun q =>
      (∑ a,∑ b,flatA (h q.2) A i q a b*spatialDD (pull A i p) q (realVec a) (realVec b))+
        ∑ a,flatB (h q.2) A i q a*spatialD (pull A i p) q (realVec a)) Q :=
    (ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ =>
      (F05_contDiffOn_matrix_entry hCoeff.1 a b).mul (hDD a b)))).add
        (ContDiffOn.sum (fun a _ => (hCoeff.2 a).mul (hD a)))
  apply hExpr.congr
  intro q hq
  have hSlice : ContDiffOn ℝ ∞ (fun z => p (lift A i z) q.2) (Metric.ball 0 3) :=
    hφ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz,hq.2⟩)
  exact F05_flattened_laplacian_C2 hA (h q.2) i (fun y => p y q.2) hq.1
    ((hSlice.contDiffAt (Metric.isOpen_ball.mem_nhds hq.1)).of_le (by simp))

end Yau.Proofs.F05Aux
