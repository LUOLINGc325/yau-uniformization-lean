import Yau.Proofs.D02GriffithsOne
import Yau.LeafProofs.L14BundleCurvature

/-! The original curvature condition supplies Griffiths nonnegativity of the
actual pullback metric in every valid atlas chart. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder Bundle

namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs.L14Aux
set_option backward.isDefEq.respectTransparency false

theorem tangentPullbackMetric_griffithsNonnegative {n : ℕ} (X : KahlerManifold n)
    {B : ComplexManifold 1}
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier X.manifold.Carrier ⊤) :
    BundleDbar.GriffithsNonnegative (r := n) (tangentPullbackFiber f)
      (tangentPullbackMetric X.metric.form f) := by
  intro a z hz ξ v
  let E := tangentPullbackFiber f
  let k := tangentPullbackMetric X.metric.form f
  let x := chartInv a z
  let A := bundleFrameTransitionMatrix (r := n) E a x x
  let d := fderiv ℂ (fun w => chartPt x (chartInv a w)) z (stdVec 0) 0
  let R := BundleDbar.curvature (r := n) E k x (chartPt x x) 0 0
  have hself : x ∈ bundleChartSource (r := n) E x :=
    ⟨mem_extChartAt_source x, mem_baseSet_trivializationAt (ComplexVector n) E x⟩
  have ho : z ∈ bundleChartOverlap (r := n) E x a := ⟨hz, hself⟩
  have ht := curvature_overlap E (tangentPullback_holomorphic f) k
    (tangentPullbackMetric_smooth X.metric.form
      (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) f) x a z ho 0 0
  have hcurv : BundleDbar.curvature (r := n) E k a z 0 0 =
      Aᴴ * ((d * star d) • R) * A := by
    simpa only [Fin.sum_univ_one] using ht
  have hR : ∀ w : Fin n → ℂ, 0 ≤ (star w ⬝ᵥ R *ᵥ w).re := by
    intro w
    have hc := tangentPullback_griffiths_center X f x (stdVec 0) (WithLp.toLp 2 w)
    rw [griffithsQuadratic_one] at hc
    simpa only [stdVec, PiLp.single_apply, ite_true, norm_one, one_pow, one_mul,
      WithLp.ofLp_toLp] using hc
  have hp := griffiths_one_congruence_nonneg R A d hR ξ v
  rw [griffithsQuadratic_one] at hp ⊢
  rw [hcurv]
  exact hp

end Yau.NodeProofs.D02Aux
