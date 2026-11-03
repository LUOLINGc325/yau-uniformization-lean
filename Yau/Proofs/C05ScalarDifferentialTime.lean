import Yau.Proofs.C05SpaceTimeDerivative
import Yau.Proofs.C05FlowRegularity

/-! The actual scalar differential commutes with physical time in
one fixed chart, on the original open positive-time interval. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Set Filter
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem hasDerivAt_rDeriv_of_smoothSpaceTime {u : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hu : SmoothSpaceTime u I) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) {t : ℝ} (ht : t ∈ I) (a : RIdx n) :
    HasDerivAt (fun s => rDeriv (inChart c (fun y => u y s)) z a)
      (rDeriv (inChart c (fun y => timeDeriv u y t)) z a) t := by
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv c p.1) p.2
  have hO : IsOpen (chartTarget c ×ˢ I) :=
    (isOpen_extChartAt_target (I := ComplexModel n) c).prod hI
  have hF : ContDiffOn ℝ ∞ F (chartTarget c ×ˢ I) := hu c
  have hFat : ContDiffAt ℝ ∞ F (z, t) := hF.contDiffAt (hO.mem_nhds ⟨hz, ht⟩)
  have hsp : ContDiffAt ℝ 1 (directionalDerivative (realVec a, 0) F) (z, t) :=
    contDiffAt_directionalDerivative hFat (by simp) (realVec a, 0)
  have htm : ContDiffAt ℝ 1 (directionalDerivative (0, 1) F) (z, t) :=
    contDiffAt_directionalDerivative hFat (by simp) (0, 1)
  have hd := right_hasDerivAt (hsp.differentiableAt one_ne_zero)
  rw [directionalDerivative_commute (hFat.of_le (by simp))] at hd
  have he : (fun w => directionalDerivative (0, 1) F (w, t)) =ᶠ[𝓝 z]
      inChart c (fun y => timeDeriv u y t) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
    have hFw : ContDiffAt ℝ ∞ F (w, t) := hF.contDiffAt
      (hO.mem_nhds (show (w, t) ∈ chartTarget c ×ˢ I from ⟨hw, ht⟩))
    exact (right_hasDerivAt (hFw.differentiableAt (by simp))).deriv.symm
  have htarget : directionalDerivative (realVec a, 0) (directionalDerivative (0, 1) F) (z, t) =
      rDeriv (inChart c (fun y => timeDeriv u y t)) z a := by
    rw [← left_directionalDerivative (htm.differentiableAt one_ne_zero)]
    exact congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec a)) he.fderiv_eq
  rw [htarget] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hI.mem_nhds ht] with s hs
  have hFs : ContDiffAt ℝ ∞ F (z, s) := hF.contDiffAt
    (hO.mem_nhds (show (z, s) ∈ chartTarget c ×ˢ I from ⟨hz, hs⟩))
  exact left_directionalDerivative (hFs.differentiableAt (by simp)) (realVec a)

end Yau.Proofs.C05Aux
