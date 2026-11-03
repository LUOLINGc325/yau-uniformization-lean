import Yau.Proofs.F05JetSpatialRealization
import Yau.Proofs.F05JetTimeRealization
import Yau.Proofs.F05RegionGeometry

/-! Equality of actual ambient values with a physical FTC jet determines
the genuine derivatives, including the closed physical and initial faces. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_realizeDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_realizeDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_realizeHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_realizeHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

theorem F05LocalFTCGraph_realization (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 < T) (u : F05LocalFTCGraph A i α hT.le)
    (v : Point n → ℝ) (hValue : EqOn v (F05BCFFun u.val.1) (F05Q A i T))
    (hv : ∀ p ∈ F05Q A i T, ContDiffAt ℝ 2 (fun z => v (z,p.2)) p.1) :
    C2 (F05Q A i T) v ∧
      EqOn (spatialD v) (F05BCFFun u.val.2.1) (F05Q A i T) ∧
      EqOn (spatialDD v) (F05BCFFun u.val.2.2.1.val.1) (F05Q A i T) ∧
      EqOn (timeD (F05Q A i T) v) (F05BCFFun u.val.2.2.2.val.1) (F05Q A i T) := by
  have hG : EqOn (spatialD v) (F05BCFFun u.val.2.1) (F05Q A i T) := by
    intro p hp
    have hGiven := F05LocalFTCGraph_hasFDerivWithinAt_value A i α hT.le u ⟨p.2,hp.2⟩ hp.1
    rw [← F05BCFFun_apply u.val.2.1 ⟨p,hp⟩] at hGiven
    have hActual := ((hv p hp).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
      (s := F05D A i)
    have hMatch := hGiven.congr' (fun z hz => hValue ⟨hz,hp.2⟩) hp.1
    exact (F05D_uniqueDiffOn A i p.1 hp.1).eq hActual hMatch
  have hH : EqOn (spatialDD v) (F05BCFFun u.val.2.2.1.val.1) (F05Q A i T) := by
    intro p hp
    have hGiven := F05LocalFTCGraph_hasFDerivWithinAt_gradient A i α hT.le u ⟨p.2,hp.2⟩ hp.1
    rw [← F05BCFFun_apply u.val.2.2.1.val.1 ⟨p,hp⟩] at hGiven
    have hActual := (((hv p hp).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt (s := F05D A i)
    have hMatch := hGiven.congr' (fun z hz => hG ⟨hz,hp.2⟩) hp.1
    exact (F05D_uniqueDiffOn A i p.1 hp.1).eq hActual hMatch
  have hTime (p : Point n) (hp : p ∈ F05Q A i T) :
      HasDerivWithinAt (fun r => v (p.1,r)) (F05BCFFun u.val.2.2.2.val.1 p) (Icc 0 T) p.2 := by
    exact (F05LocalFTCGraph_hasDerivWithinAt_raw_time A i α hT.le u hp.1 hp.2).congr_of_mem
      (fun r hr => hValue ⟨hp.1,hr⟩) hp.2
  have hFiber (p : Point n) (hp : p ∈ F05Q A i T) :
      {r | (p.1,r) ∈ F05Q A i T} = Icc 0 T := by
    ext r
    change (p.1 ∈ F05D A i ∧ r ∈ Icc 0 T) ↔ r ∈ Icc 0 T
    exact and_iff_right hp.1
  have hK : EqOn (timeD (F05Q A i T) v) (F05BCFFun u.val.2.2.2.val.1) (F05Q A i T) := by
    intro p hp
    unfold timeD
    rw [hFiber p hp]
    exact (hTime p hp).derivWithin (uniqueDiffOn_Icc hT p.2 hp.2)
  refine ⟨⟨(F05BCFFun_continuousOn u.val.1).congr hValue,
    (F05BCFFun_continuousOn u.val.2.1).congr hG,
    (F05BCFFun_continuousOn u.val.2.2.1.val.1).congr hH,
    (F05BCFFun_continuousOn u.val.2.2.2.val.1).congr hK,hv,?_⟩,hG,hH,hK⟩
  intro p hp
  rw [hFiber p hp]
  exact (hTime p hp).differentiableWithinAt

end Yau.Proofs.F05Aux
