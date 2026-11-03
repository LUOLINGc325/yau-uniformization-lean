import Yau.Proofs.D02PullbackCurvature
import Yau.Proofs.D02PotentialLevi
import Yau.Proofs.G01BisectionalNormalization

/-! The original paper curvature sign gives the actual pullback curvature
sign at every centered chart. No curvature hypothesis is added. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder Bundle

namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem kahlerManifold_nonnegBisectional {n : ℕ} (X : KahlerManifold n) :
    NonnegBisectional X.metric.form := by
  have hs := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  have hp := (G01Aux.paperPositive_iff_griffithsPositive X.metric.form hs X.kahler_metric).mp
    X.positive_bisectional_curvature
  intro x v w
  by_cases hv : v = 0
  · subst v; simp [bisectionalForm]
  · by_cases hw : w = 0
    · subst w; simp [bisectionalForm]
    · exact (hp x v w hv hw).le

theorem curvatureMatrix_hMat_center {n : ℕ} {M : ComplexManifold n}
    (g : HermitianField M) (hg : MetricSmooth g) (x : M.Carrier)
    (p q α β : Fin n) :
    BundleDbar.curvatureMatrix (hMat g x) (chartPt x x) p q α β =
      chernCurvature g x β α p q := by
  calc
    _ = (hMat g x (chartPt x x) * G01Aux.chernF g x (chartPt x x) p q) α β := by
      simp only [G01Aux.chernF, Matrix.mul_neg]
      rfl
    _ = _ := G01Aux.chernF_lower g hg x (chartPt x x) (mem_extChartAt_target x) β α p q

theorem tangentPullback_griffiths_center {n : ℕ} (X : KahlerManifold n)
    {B : ComplexManifold 1}
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier X.manifold.Carrier ⊤)
    (a : B.Carrier) (ξ : ComplexVector 1) (v : ComplexVector n) :
    0 ≤ BundleDbar.griffithsQuadratic
      (BundleDbar.curvature (r := n) (tangentPullbackFiber f)
        (tangentPullbackMetric X.metric.form f) a (chartPt a a)) ξ v := by
  have hg := Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric
  have hround : chartInv a (chartPt a a) = a :=
    (extChartAt (ComplexModel 1) a).left_inv (mem_extChartAt_source a)
  have hz : chartPt a a ∈ BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a := by
    refine ⟨mem_extChartAt_target a, ?_⟩
    change chartInv a (chartPt a a) ∈
      (BundleDbar.localTriv (r := n) (tangentPullbackFiber f) a).baseSet
    rw [hround]
    exact mem_baseSet_trivializationAt (ComplexVector n) (tangentPullbackFiber f) a
  have ht : tangentPullbackChartMap f a (chartPt a a) = chartPt (f a) (f a) := by
    change chartPt (f a) (f (chartInv a (chartPt a a))) = _
    rw [hround]
  let J := fderiv ℂ (tangentPullbackChartMap f a) (chartPt a a) (stdVec 0)
  have he : BundleDbar.griffithsQuadratic
      (BundleDbar.curvature (r := n) (tangentPullbackFiber f)
        (tangentPullbackMetric X.metric.form f) a (chartPt a a)) ξ v =
      bisectionalForm X.metric.form (f a) v (ξ 0 • J) := by
    unfold BundleDbar.griffithsQuadratic bisectionalForm
    simp only [Fin.sum_univ_one]
    simp_rw [tangentPullback_curvature X.metric.form hg f a (chartPt a a) hz,
      ht, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      curvatureMatrix_hMat_center X.metric.form hg (f a), Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro α _
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    simp only [J, PiLp.smul_apply, smul_eq_mul, star_mul]
    ring
  rw [he]
  exact kahlerManifold_nonnegBisectional X (f a) v (ξ 0 • J)

end Yau.NodeProofs.D02Aux
