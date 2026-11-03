import Yau.Proofs.D02PullbackFrames

/-! Regularity of the computed metric and differential in the actual pullback
atlas. No frame, transition matrix, metric coefficient, or dF coefficient is
provided by the caller. -/

open scoped Manifold Topology ContDiff Matrix Bundle
open Bundle

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n} {B : ComplexManifold 1}

def tangentPullbackChartMap
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a : B.Carrier) (z : ComplexVector 1) : ComplexVector n :=
  chartPt (f a) (f (chartInv a z))

theorem tangentPullback_localDomain_isOpen
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a : B.Carrier) :
    IsOpen (BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a) :=
  (continuousOn_extChartAt_symm (I := ComplexModel 1) a).isOpen_inter_preimage
    (isOpen_extChartAt_target (I := ComplexModel 1) a)
    (BundleDbar.localTriv (r := n) (tangentPullbackFiber f) a).open_baseSet

theorem tangentPullbackChartMap_mapsTo
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a : B.Carrier) : Set.MapsTo (tangentPullbackChartMap f a)
      (BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a) (chartTarget (f a)) := by
  intro z hz
  have ht : f (chartInv a z) ∈ (chartAt (ComplexVector n) (f a)).source := hz.2
  apply (extChartAt (ComplexModel n) (f a)).map_source
  simpa only [extChartAt_source] using ht

theorem tangentPullbackChartMap_differentiableOn
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a : B.Carrier) : DifferentiableOn ℂ (tangentPullbackChartMap f a)
      (BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := ComplexModel 1) (n := ∞) a).mdifferentiableOn
    (by simp)).mono
      (show BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a ⊆ chartTarget a from
        fun _ hz => hz.1)
  have hf := f.contMDiff.mdifferentiable (by simp)
  have hf' : MDifferentiableOn (ComplexModel 1) (ComplexModel n) f Set.univ :=
    hf.mdifferentiableOn
  have hh := hf'.comp hi (fun _ _ => Set.mem_univ _)
  have hc := (mdifferentiableOn_extChartAt (I := ComplexModel n) (x := f a)).comp hh
    (fun z hz => (show f (chartInv a z) ∈
      (chartAt (ComplexVector n) (f a)).source from hz.2))
  exact hc.differentiableOn

theorem tangentPullbackMetric_smooth (g : HermitianField M) (hg : MetricSmooth g)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤) :
    BundleDbar.SmoothMetric (r := n) (tangentPullbackFiber f) (tangentPullbackMetric g f) := by
  intro a i j
  have hc : ContDiffOn ℝ ∞ (tangentPullbackChartMap f a)
      (BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a) :=
    (complex_holomorphic_contDiffOn (tangentPullback_localDomain_isOpen f a)
      (tangentPullbackChartMap_differentiableOn f a)).restrict_scalars ℝ
  have hH := (Yau.LeafProofs.L17Aux.hMat_contDiffOn_of_metricSmooth g hg (f a) i j).comp
    hc (tangentPullbackChartMap_mapsTo f a)
  exact hH.congr fun z hz => congrFun (congrFun (tangentPullback_metricMatrix g f a hz) i) j

theorem tangentPullbackMap_holomorphic {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤) :
    BundlePresentation.HolomorphicMap (r := n) (tangentPullbackFiber f)
      (tangentPullbackMap F f) := by
  intro a
  have hJ : DifferentiableOn ℂ
      (fun z => immersionDerivativeMatrix F (f a) (tangentPullbackChartMap f a z))
      (BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a) :=
    differentiableOn_pi.mpr fun i => differentiableOn_pi.mpr fun j =>
      (immersionDerivativeMatrix_differentiableOn hF (f a) i j).comp
        (tangentPullbackChartMap_differentiableOn f a) (tangentPullbackChartMap_mapsTo f a)
  exact hJ.congr fun z hz => tangentPullback_mapCoefficients hF f a hz

end Yau.NodeProofs.D02Aux
