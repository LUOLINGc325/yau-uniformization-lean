import Yau.Proofs.F05JetRealization
import Yau.LeafProofs.L16

/-! The actual FTC kernels determine all four jet components from the
values, including at the physical boundary and the initial time. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05LocalFTCGraph_ext_values (A : AtlasData M) (i : Fin A.count) (α : ℝ)
    {T : ℝ} (hT : 0 < T) {u v : F05LocalFTCGraph A i α hT.le}
    (hValue : ∀ p : F05Q A i T, u.val.1 p = v.val.1 p) : u = v := by
  have hRawV {p : Point n} (hp : p ∈ F05Q A i T) : F05BCFFun u.val.1 p = F05BCFFun v.val.1 p := by
    rw [F05BCFFun_apply _ ⟨p,hp⟩,F05BCFFun_apply _ ⟨p,hp⟩]
    exact hValue ⟨p,hp⟩
  have hGradient (p : F05Q A i T) : u.val.2.1 p = v.val.2.1 p := by
    have hU := F05LocalFTCGraph_hasFDerivWithinAt_value A i α hT.le u ⟨p.val.2,p.property.2⟩ (z := p.val.1) p.property.1
    have hV := F05LocalFTCGraph_hasFDerivWithinAt_value A i α hT.le v ⟨p.val.2,p.property.2⟩ (z := p.val.1) p.property.1
    have hMatch : HasFDerivWithinAt (fun z => F05BCFFun v.val.1 (z,p.val.2))
        (u.val.2.1 p) (F05D A i) p.val.1 :=
      hU.congr' (fun z hz => (hRawV (p := (z,p.val.2)) ⟨hz,p.property.2⟩).symm) p.property.1
    exact (F05D_uniqueDiffOn A i p.val.1 p.property.1).eq hMatch hV
  have hRawG {p : Point n} (hp : p ∈ F05Q A i T) : F05BCFFun u.val.2.1 p = F05BCFFun v.val.2.1 p := by
    rw [F05BCFFun_apply _ ⟨p,hp⟩,F05BCFFun_apply _ ⟨p,hp⟩]
    exact hGradient ⟨p,hp⟩
  have hHessian (p : F05Q A i T) : u.val.2.2.1.val.1 p = v.val.2.2.1.val.1 p := by
    have hU := F05LocalFTCGraph_hasFDerivWithinAt_gradient A i α hT.le u ⟨p.val.2,p.property.2⟩ (z := p.val.1) p.property.1
    have hV := F05LocalFTCGraph_hasFDerivWithinAt_gradient A i α hT.le v ⟨p.val.2,p.property.2⟩ (z := p.val.1) p.property.1
    have hMatch : HasFDerivWithinAt (fun z => F05BCFFun v.val.2.1 (z,p.val.2))
        (u.val.2.2.1.val.1 p) (F05D A i) p.val.1 :=
      hU.congr' (fun z hz => (hRawG (p := (z,p.val.2)) ⟨hz,p.property.2⟩).symm) p.property.1
    exact (F05D_uniqueDiffOn A i p.val.1 p.property.1).eq hMatch hV
  have hTime (p : F05Q A i T) : u.val.2.2.2.val.1 p = v.val.2.2.2.val.1 p := by
    have hU := F05LocalFTCGraph_hasDerivWithinAt_raw_time A i α hT.le u (z := p.val.1) p.property.1 (t := p.val.2) p.property.2
    have hV := F05LocalFTCGraph_hasDerivWithinAt_raw_time A i α hT.le v (z := p.val.1) p.property.1 (t := p.val.2) p.property.2
    have hMatch : HasDerivWithinAt (fun t => F05BCFFun v.val.1 (p.val.1,t))
        (F05BCFFun u.val.2.2.2.val.1 p.val) (Icc 0 T) p.val.2 := hU.congr_of_mem
      (fun t ht => (hRawV (p := (p.val.1,t)) ⟨p.property.1,ht⟩).symm) p.property.2
    have hEqual := UniqueDiffWithinAt.eq_deriv (Icc 0 T) (uniqueDiffOn_Icc hT p.val.2 p.property.2) hMatch hV
    simpa only [F05BCFFun_apply _ p] using hEqual
  apply Subtype.ext
  apply Prod.ext (BoundedContinuousFunction.ext hValue)
  apply Prod.ext (BoundedContinuousFunction.ext hGradient)
  exact Prod.ext (vectorHolderGraph_ext hHessian) (holderGraph_ext hTime)

end Yau.Proofs.F05Aux
