import Yau.Proofs.Y03MetricSmooth
import Yau.Proofs.Y03JointPullback
import Yau.Proofs.Y03ComplexStrip

/-! Joint Levi positivity on the actual smooth flow gives the bounded-strip norm comparison. -/

open scoped Topology
open Set

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X} {h : Flow X} {U P ρ : STF X}

theorem jointPositiveClock_flow_curve {γ : ℂ → ComplexVector n × ComplexVector n × ℂ} {z : ℂ}
    (hflow : FlowStage X o h U P ρ) (hjoint : JointPositiveClock X h) (x : Pt X)
    (hγ : ContDiffAt ℂ 2 γ z) (hq : (γ z).1 ∈ chartTarget x) :
    0 ≤ (wirt (fun p => wirtBar (fun q : ℂ =>
      (dualNormChart (h (Real.exp (2 * (γ q).2.2.re))) x (γ q).1 (γ q).2.1 : ℂ)) p 1) z 1).re := by
  exact jointPositiveClock_holomorphic_pullback hjoint x γ z hγ hq
    ((dualNormClock_joint_contDiffAt hflow.1.1.2.1 x (γ z) hq).of_le (by norm_num))

theorem jointPositiveClock_bounded_strip
    (hflow : FlowStage X o h U P ρ) (hjoint : JointPositiveClock X h) (x : Pt X)
    (γ : ℂ → ComplexVector n × ComplexVector n × ℂ) (T B C : ℝ) (hT : 0 < T)
    (hγ : ∀ z : ℂ, ContDiffAt ℂ 2 γ z)
    (hchart : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T → (γ z).1 ∈ chartTarget x)
    (hbound : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T →
      dualNormChart (h (Real.exp (2 * (γ z).2.2.re))) x (γ z).1 (γ z).2.1 ≤ C)
    (hleft : ∀ y : ℝ,
      dualNormChart (h (Real.exp (2 * (γ ((y : ℂ) * Complex.I)).2.2.re))) x
        (γ ((y : ℂ) * Complex.I)).1 (γ ((y : ℂ) * Complex.I)).2.1 ≤ B)
    (hright : ∀ y : ℝ,
      dualNormChart (h (Real.exp (2 * (γ ((T : ℂ) + (y : ℂ) * Complex.I)).2.2.re))) x
        (γ ((T : ℂ) + (y : ℂ) * Complex.I)).1
        (γ ((T : ℂ) + (y : ℂ) * Complex.I)).2.1 ≤ B) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T →
      dualNormChart (h (Real.exp (2 * (γ z).2.2.re))) x (γ z).1 (γ z).2.1 ≤ B := by
  let f : ComplexVector n × ComplexVector n × ℂ → ℝ := fun p =>
    dualNormChart (h (Real.exp (2 * p.2.2.re))) x p.1 p.2.1
  have hsmooth : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ T → ContDiffAt ℝ 2 (f ∘ γ) z := by
    intro z hz₀ hzT
    have hf := dualNormClock_joint_contDiffAt hflow.1.1.2.1 x (γ z) (hchart z hz₀ hzT)
    have hf2 : ContDiffAt ℝ 2 f (γ z) := hf.of_le (by norm_num)
    exact hf2.comp z ((hγ z).restrict_scalars ℝ)
  apply bounded_complex_strip_maximum hT
  · intro z hz
    exact (hsmooth z hz.1 hz.2).continuousAt.continuousWithinAt
  · intro z hz₀ hzT
    exact hsmooth z hz₀.le hzT.le
  · intro z hz₀ hzT
    exact jointPositiveClock_flow_curve hflow hjoint x (hγ z) (hchart z hz₀.le hzT.le)
  · exact hbound
  · exact hleft
  · exact hright

end Yau.Blueprint.Alignment.Y03Proof
