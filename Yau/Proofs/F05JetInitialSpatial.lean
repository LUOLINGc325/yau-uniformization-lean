import Yau.Proofs.F05JetZeroData
import Yau.Proofs.F05JetSpatialRealization
import Yau.Proofs.F05RegionGeometry

/-! A zero physical initial value forces the actual initial gradient and
Hessian to vanish, including the physical boundary. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_initialDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_initialDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_initialHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_initialHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

theorem F05LocalZeroFTCGraph_initial_gradient (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalZeroFTCGraph A i α hT)
    {z : Space n} (hz : z ∈ F05D A i) :
    u.val.2.1 ⟨(z,0),hz,le_rfl,hT⟩ = 0 := by
  have hD := F05LocalFTCGraph_hasFDerivWithinAt_value A i α hT
    (F05LocalZeroToFTC A i α hT u) ⟨0,le_rfl,hT⟩ hz
  change HasFDerivWithinAt (fun w => F05BCFFun u.val.1 (w,0))
    (u.val.2.1 ⟨(z,0),hz,le_rfl,hT⟩) (F05D A i) z at hD
  have hValue (w : Space n) (hw : w ∈ F05D A i) : F05BCFFun u.val.1 (w,0) = 0 := by
    rw [F05BCFFun_apply u.val.1 ⟨(w,0),hw,le_rfl,hT⟩]
    exact F05LocalZeroFTCGraph_initial_value A i α hT u ⟨w,hw⟩
  have hZero : HasFDerivWithinAt (fun w => F05BCFFun u.val.1 (w,0))
      (0 : F05Dual n) (F05D A i) z :=
    (hasFDerivWithinAt_const (0 : ℝ) z (F05D A i)).congr' hValue hz
  exact (F05D_uniqueDiffOn A i z hz).eq hD hZero

theorem F05LocalZeroFTCGraph_initial_hessian (A : AtlasData M) (i : Fin A.count)
    (α : ℝ) {T : ℝ} (hT : 0 ≤ T) (u : F05LocalZeroFTCGraph A i α hT)
    {z : Space n} (hz : z ∈ F05D A i) :
    u.val.2.2.1.val.1 ⟨(z,0),hz,le_rfl,hT⟩ = 0 := by
  have hD := F05LocalFTCGraph_hasFDerivWithinAt_gradient A i α hT
    (F05LocalZeroToFTC A i α hT u) ⟨0,le_rfl,hT⟩ hz
  change HasFDerivWithinAt (fun w => F05BCFFun u.val.2.1 (w,0))
    (u.val.2.2.1.val.1 ⟨(z,0),hz,le_rfl,hT⟩) (F05D A i) z at hD
  have hGradient (w : Space n) (hw : w ∈ F05D A i) : F05BCFFun u.val.2.1 (w,0) = 0 := by
    rw [F05BCFFun_apply u.val.2.1 ⟨(w,0),hw,le_rfl,hT⟩]
    exact F05LocalZeroFTCGraph_initial_gradient A i α hT u hw
  have hZero : HasFDerivWithinAt (fun w => F05BCFFun u.val.2.1 (w,0))
      (0 : F05Hessian n) (F05D A i) z :=
    (hasFDerivWithinAt_const (0 : F05Dual n) z (F05D A i)).congr' hGradient hz
  exact (F05D_uniqueDiffOn A i z hz).eq hD hZero

end Yau.Proofs.F05Aux
