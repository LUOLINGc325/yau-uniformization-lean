import Yau.Proofs.C03MovingEnergyJets
import Yau.Proofs.C03CovariantTimeDifference

/-! The actual radial acceleration of the polynomial family has the
prescribed linear-in-time quadratic correction at zero parameter. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem movingJoint_second_parameter_jet
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n) {a : ℂ} {t : ℝ}
    (hZ : ContDiffAt ℝ 2 (movingJoint γ W Q) (a, t)) (v w : ℂ) :
    mapDirection (mapDirection (movingJoint γ W Q) (v, 0)) (w, 0) (a, t) =
      (v * ((t : ℂ) * w)) • Q := by
  rw [mapDirection_parameter_second _ hZ]
  exact movingTrial_second_mapDirection γ W Q t a v w

theorem movingJoint_radial_acceleration_zero_parameter
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (γ W : ℝ → ComplexVector n) (Q : ComplexVector n) {t : ℝ}
    (hZ : ContDiffAt ℝ 2 (movingJoint γ W Q) (0, t)) (v : ℂ) :
    mapCovariantD Γ (movingJoint γ W Q) (v, 0)
      (mapDirection (movingJoint γ W Q) (v, 0)) (0, t) =
      t • (v ^ 2 • Q) + Γ (γ t) (v • W t) (v • W t) := by
  unfold mapCovariantD
  rw [movingJoint_second_parameter_jet γ W Q hZ,
    movingJoint_parameter_jet γ W Q (hZ.differentiableAt (by norm_num))]
  simp only [mul_zero, zero_smul, add_zero, movingJoint, movingTrial_zero_parameter]
  congr 1
  rw [← smul_assoc t (v ^ 2 : ℂ) Q, Complex.real_smul]
  congr 1
  ring

end Yau.Proofs.C03Aux
