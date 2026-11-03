import spec.CHAIN.CONTRACTS
import Yau.Proofs.Y03JointPullback
import Yau.Proofs.Y03MetricSmooth

/-!
The first C01 input is the actual joint Levi matrix produced by E03.  These
lemmas use the smoothness of the same localized flow and do not require its
positive-time completeness, a curvature bound, or the later chart contracts.
-/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint Yau.BlueprintContracts

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_metricSmooth
    (hflow : LocalizedFlow X o h U P ρ) {t : ℝ} (ht : 0 ≤ t) :
    MetricSmooth (h t) := by
  intro x a b
  exact (hflow.1.2.1 x a b).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun z hz => ⟨hz, ht⟩)

theorem jointPositivity_clock
    (hjoint : JointPositivity X h) : Alignment.JointPositiveClock X h :=
  hjoint.1

/-- E03 controls every actual complex direction, including the freely
chosen first derivative of the cotangent vector. -/
theorem localizedFlow_jointLevi_direction
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (q : ComplexVector n × ComplexVector n × ℂ)
    (hq : q.1 ∈ chartTarget x) (v : ComplexVector n × ComplexVector n × ℂ) :
    0 ≤ (wirt (fun p => wirtBar
      (fun p : ComplexVector n × ComplexVector n × ℂ =>
        (dualNormChart (h (Real.exp (2 * p.2.2.re))) x p.1 p.2.1 : ℂ)) p v) q v).re := by
  exact Alignment.Y03Proof.jointPositiveClock_direction
    (jointPositivity_clock hjoint) x q hq
    ((Alignment.Y03Proof.dualNormClock_joint_contDiffAt hflow.1.2.1 x q hq).of_le
      (by norm_num)) v

/-- The original parent is instantiated at precisely the supplied localized
flow, without introducing a second flow or a freely chosen Harnack premise. -/
theorem localizedFlow_jointLevi_direction_of_E03
    (hE03 : E03_contract) (hflow : LocalizedFlow X o h U P ρ)
    (x : Pt X) (q : ComplexVector n × ComplexVector n × ℂ)
    (hq : q.1 ∈ chartTarget x) (v : ComplexVector n × ComplexVector n × ℂ) :
    0 ≤ (wirt (fun p => wirtBar
      (fun p : ComplexVector n × ComplexVector n × ℂ =>
        (dualNormChart (h (Real.exp (2 * p.2.2.re))) x p.1 p.2.1 : ℂ)) p v) q v).re := by
  exact localizedFlow_jointLevi_direction hflow
    (hE03 n X o h U P ρ hflow) x q hq v

/-- Joint positivity can be tested on a holomorphic curve with an arbitrary
cotangent jet; all regularity comes from the original flow. -/
theorem localizedFlow_jointLevi_curve
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (γ : ℂ → ComplexVector n × ComplexVector n × ℂ) (z : ℂ)
    (hγ : ContDiffAt ℂ 2 γ z) (hq : (γ z).1 ∈ chartTarget x) :
    0 ≤ (wirt (fun p => wirtBar (fun q : ℂ =>
      (dualNormChart (h (Real.exp (2 * (γ q).2.2.re))) x
        (γ q).1 (γ q).2.1 : ℂ)) p 1) z 1).re := by
  exact Alignment.Y03Proof.jointPositiveClock_holomorphic_pullback
    (jointPositivity_clock hjoint) x γ z hγ hq
    ((Alignment.Y03Proof.dualNormClock_joint_contDiffAt hflow.1.2.1 x (γ z) hq).of_le
      (by norm_num))

end Yau.NodeProofs.C01Aux
