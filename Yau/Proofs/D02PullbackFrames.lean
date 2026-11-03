import Yau.Proofs.D02ManifoldHolomorphic

/-! Identifying the actual pullback atlas with the original chart differential.
The metric and map matrices below are computed in this atlas. -/

open scoped Manifold Topology ContDiff Matrix Bundle
open Bundle

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n} {B : ComplexManifold 1}

theorem tangentPullback_frame
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a x : B.Carrier)
    (hx : f x ∈ (extChartAt (ComplexModel n) (f a)).source) (v : ComplexVector n) :
    (BundleDbar.localTriv (r := n) (tangentPullbackFiber f) a).symmL ℂ x v =
      chartVec (f a) (f x) v := by
  let e := trivializationAt (ComplexVector n) (TangentSpace (ComplexModel n)) (f a)
  have helinear : e.IsLinear ℂ := by dsimp only [e]; infer_instance
  have hx' : f x ∈ (chartAt (ComplexVector n) (f a)).source := by
    simpa only [extChartAt_source] using hx
  have he : f x ∈ e.baseSet := hx'
  change (e.pullback f).symmL ℂ x v = _
  rw [(e.pullback f).symmL_apply he]
  have hp : (e.pullback f).symm x v = e.symm (f x) v := by
    have hP : ((e.pullback f) (TotalSpace.mk' (ComplexVector n) x (e.symm (f x) v))).2 = v := by
      change (e (TotalSpace.mk' (ComplexVector n) (f x) (e.symm (f x) v))).2 = v
      rw [e.apply_mk_symm he]
    calc
      (e.pullback f).symm x v = (e.pullback f).symm x
          ((e.pullback f) (TotalSpace.mk' (ComplexVector n) x (e.symm (f x) v))).2 :=
        congrArg ((e.pullback f).symm x) hP.symm
      _ = e.symm (f x) v := (e.pullback f).symm_apply_apply_mk he _
  rw [hp, ← e.symmL_apply (R := ℂ) he]
  have hframe := TangentBundle.symmL_trivializationAt (𝕜 := ℂ) (I := ComplexModel n) hx'
  rw [hframe]
  have hU : Set.range (ComplexModel n) = Set.univ := by
    ext z
    simp [ComplexModel]
  rw [hU, mfderivWithin_univ]
  rfl

theorem tangentPullback_metricMatrix (g : HermitianField M)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a : B.Carrier) {z : ComplexVector 1}
    (hz : z ∈ BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a) :
    BundleDbar.metricMatrix (r := n) (tangentPullbackFiber f) (tangentPullbackMetric g f) a z =
      hMat g (f a) (chartPt (f a) (f (chartInv a z))) := by
  have hx : f (chartInv a z) ∈ (extChartAt (ComplexModel n) (f a)).source := by
    have ht : f (chartInv a z) ∈ (chartAt (ComplexVector n) (f a)).source := hz.2
    simpa only [extChartAt_source] using ht
  have hr : chartInv (f a) (chartPt (f a) (f (chartInv a z))) = f (chartInv a z) :=
    (extChartAt (ComplexModel n) (f a)).left_inv hx
  ext i j
  change (g (f (chartInv a z))).toFun _ _ = _
  rw [tangentPullback_frame f a (chartInv a z) hx,
    tangentPullback_frame f a (chartInv a z) hx]
  change (g (f (chartInv a z))).toFun
    (chartVec (f a) (f (chartInv a z)) (stdVec i))
    (chartVec (f a) (f (chartInv a z)) (stdVec j)) =
    (g (chartInv (f a) (chartPt (f a) (f (chartInv a z))))).toFun
      (chartVec (f a) (chartInv (f a) (chartPt (f a) (f (chartInv a z)))) (stdVec i))
      (chartVec (f a) (chartInv (f a) (chartPt (f a) (f (chartInv a z)))) (stdVec j))
  rw [hr]

theorem tangentPullback_mapCoefficients {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F)
    (f : ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤)
    (a : B.Carrier) {z : ComplexVector 1}
    (hz : z ∈ BundleDbar.localDomain (r := n) (tangentPullbackFiber f) a) :
    BundlePresentation.mapCoefficients (r := n) (tangentPullbackFiber f)
      (tangentPullbackMap F f) a z =
        immersionDerivativeMatrix F (f a) (chartPt (f a) (f (chartInv a z))) := by
  have hx : f (chartInv a z) ∈ (extChartAt (ComplexModel n) (f a)).source := by
    have ht : f (chartInv a z) ∈ (chartAt (ComplexVector n) (f a)).source := hz.2
    simpa only [extChartAt_source] using ht
  ext i j
  change (NormedSpace.fromTangentSpace (𝕜 := ℂ) (F (f (chartInv a z))))
    (mfderiv (ComplexModel n) (ComplexModel N) F (f (chartInv a z)) _) i = _
  rw [tangentPullback_frame f a (chartInv a z) hx]
  have h := immersionDerivativeMatrix_apply hF (f a)
    (z := chartPt (f a) (f (chartInv a z)))
    ((extChartAt (ComplexModel n) (f a)).map_source hx) i j
  have hr : chartInv (f a) (chartPt (f a) (f (chartInv a z))) = f (chartInv a z) :=
    (extChartAt (ComplexModel n) (f a)).left_inv hx
  rw [hr] at h
  exact h.symm

end Yau.NodeProofs.D02Aux
