import Yau.Proofs.F05SmoothLaplacian

/-! Actual finite C2 regularity is enough for continuity of the computed
Laplacian on every closed physical chart. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_pull_laplacian_continuous_C2 {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (u : M.Carrier → ℝ → ℝ)
    {T : ℝ} (hh : MetricFamilySmooth h (Icc 0 T)) (i : Fin A.count)
    (hu : C2 (F05Q A i T) (pull A i u)) :
    ContinuousOn (pull A i (fun x t => laplacian (h t) (fun y => u y t) x)) (F05Q A i T) := by
  have hSub : F05Q A i T ⊆ Metric.ball 0 3 ×ˢ Icc 0 T := fun q hq => ⟨F05D_mem_ball hq.1,hq.2⟩
  have hCoeff := F05_flat_coefficients_smooth hA h hh i
  have hD (a : RIdx n) : ContinuousOn (fun q => spatialD (pull A i u) q (realVec a)) (F05Q A i T) :=
    hu.2.1.clm_apply continuousOn_const
  have hDD (a b : RIdx n) : ContinuousOn (fun q => spatialDD (pull A i u) q (realVec a) (realVec b)) (F05Q A i T) :=
    (hu.2.2.1.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hExpr : ContinuousOn (fun q =>
      (∑ a,∑ b,flatA (h q.2) A i q a b*spatialDD (pull A i u) q (realVec a) (realVec b))+
        ∑ a,flatB (h q.2) A i q a*spatialD (pull A i u) q (realVec a)) (F05Q A i T) :=
    (continuousOn_finset_sum Finset.univ (fun a _ => continuousOn_finset_sum Finset.univ (fun b _ =>
      ((F05_contDiffOn_matrix_entry hCoeff.1 a b).continuousOn.mono hSub).mul (hDD a b)))).add
        (continuousOn_finset_sum Finset.univ (fun a _ => ((hCoeff.2 a).continuousOn.mono hSub).mul (hD a)))
  apply hExpr.congr
  intro q hq
  exact F05_flattened_laplacian_C2 hA (h q.2) i (fun y => u y q.2) (F05D_mem_ball hq.1)
    (hu.2.2.2.2.1 q hq)

end Yau.Proofs.F05Aux
