import Yau.Proofs.F05CoordinateCoefficients

/-! Exact local C2 transport of the original Laplacian through the genuine
flattening maps. The first-order chart-curvature term is retained. -/

open Set Filter
open scoped Topology ContDiff Manifold Matrix
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_flattened_laplacian_C2 {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : HermitianField M) (i : Fin A.count)
    (f : M.Carrier → ℝ) {z : Space n} (hz : z ∈ Metric.ball 0 3)
    (hf : ContDiffAt ℝ 2 (fun y => f (lift A i y)) z) :
    laplacian h f (lift A i z) =
      (∑ a, ∑ b, flatA h A i (z,0) a b *
        fderiv ℝ (fderiv ℝ (fun y => f (lift A i y))) z (realVec a) (realVec b)) +
      ∑ a, flatB h A i (z,0) a * fderiv ℝ (fun y => f (lift A i y)) z (realVec a) := by
  let x := A.inverse i z
  let F := A.forward i
  let v : Space n → ℝ := fun y => f (lift A i y)
  have hx : x ∈ A.source i := (hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩
  have hxt := (hA.1 i).2.1 hx
  have hForward : F x = z := (hA.1 i).2.2.2.2.2.1 z hz
  have hF : ContDiffAt ℝ 2 F x :=
    (((hA.1 i).2.2.1).contDiffAt ((hA.1 i).1.mem_nhds hx)).of_le (by simp)
  have hv : ContDiffAt ℝ 2 v (F x) := by rw [hForward]; exact hf
  have heq : inChart (A.center i) f =ᶠ[𝓝 x] (fun y => v (F y)) := by
    filter_upwards [(hA.1 i).1.mem_nhds hx] with y hy
    change f (chartInv (A.center i) y) =
      f (chartInv (A.center i) (A.inverse i (A.forward i y)))
    rw [(hA.1 i).2.2.2.2.2.2.1 y hy]
  have hRaw : ContDiffAt ℝ 2 (inChart (A.center i) f) x :=
    (hv.comp x hF).congr_of_eventuallyEq heq
  have hH := ((heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)).trans
    (secondFDeriv_chart_comp hF hv)
  rw [hForward] at hH
  have hPrincipal := chartPrincipalMatrix_contraction (fderiv ℝ F x)
    (baseA h (A.center i) x) (fderiv ℝ (fderiv ℝ v) z)
  have hDrift := chartDriftVector_contraction (fderiv ℝ F x)
    (fderiv ℝ (fderiv ℝ F) x) (baseA h (A.center i) x) (fun _ => 0) (fderiv ℝ v z)
  simp only [zero_mul,Finset.sum_const_zero,add_zero] at hDrift
  change laplacian h f (chartInv (A.center i) x) = _
  rw [F05_laplacian_chart_C2 h (A.center i) f hxt hRaw,hH]
  rw [F05_flatA_chartPrincipal hA h i (z,0) hz,F05_flatB_chartDrift hA h i (z,0) hz]
  change (∑ a, ∑ b, baseA h (A.center i) x a b *
    chartSecondJet (fderiv ℝ F x) (fderiv ℝ (fderiv ℝ F) x)
      (fderiv ℝ v z) (fderiv ℝ (fderiv ℝ v) z) (realVec a) (realVec b)) = _
  simp only [chartSecondJet_apply,mul_add,Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hPrincipal.symm hDrift.symm

end Yau.Proofs.F05Aux
