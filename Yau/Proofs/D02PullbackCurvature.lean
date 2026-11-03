import Yau.Proofs.D02CurvatureComposition

/-! Curvature of the actual pullback metric, in its actual atlas. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder Bundle

namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs.L14Aux Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n} {B : ComplexManifold 1}

theorem tangentPullback_curvature (g : HermitianField M) (hg : MetricSmooth g)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a : B.Carrier) (z : ComplexVector 1)
    (hz : z ∈ BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a) (i j : Fin 1) :
    BundleDbar.curvature (r := n) (tangentPullbackFiber f) (tangentPullbackMetric g f) a z i j =
      ∑ p, ∑ q,
        (fderiv ℂ (tangentPullbackChartMap f a) z (stdVec i) p *
          star (fderiv ℂ (tangentPullbackChartMap f a) z (stdVec j) q)) •
            BundleDbar.curvatureMatrix (hMat g (f a)) (tangentPullbackChartMap f a z) p q := by
  let O := BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a
  have hO : IsOpen O := tangentPullback_localDomain_isOpen f a
  have hEq : Set.EqOn
      (BundleDbar.metricMatrix (r := n) (tangentPullbackFiber f) (tangentPullbackMetric g f) a)
      (fun w => hMat g (f a) (tangentPullbackChartMap f a w)) O :=
    fun w hw => tangentPullback_metricMatrix g f a hw
  have hcong := congrArg (fun R => R i j) (curvatureMatrix_congr_of_eqOn _ _ hO hEq z hz)
  have hT : ContDiffOn ℂ ∞ (tangentPullbackChartMap f a) O :=
    complex_holomorphic_contDiffOn hO (tangentPullbackChartMap_differentiableOn f a)
  exact hcong.trans (curvatureMatrix_comp_different_dim hO
    (isOpen_extChartAt_target (I := ComplexModel n) (f a)) (hMat g (f a))
    (tangentPullbackChartMap f a)
    (Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg (f a))
    (fun w hw => ne_of_gt (hMat_posDef g (f a) w hw).det_pos)
    hT (tangentPullbackChartMap_mapsTo f a) z hz i j)

end Yau.NodeProofs.D02Aux
