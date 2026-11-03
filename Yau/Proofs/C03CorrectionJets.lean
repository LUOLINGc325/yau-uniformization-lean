import Yau.Proofs.C03PoleLimit
import Yau.Proofs.C03PoleJets

/-! The same actual weighted correction has zero critical jets, so the entire complement
has the seed's actual value and complex first derivative. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
namespace Yau.Proofs.C03Aux.CorrectionJets
open Yau Yau.NodeProofs.P03Aux
variable {n : ℕ}

theorem correction_jets_of_coordinate_poles (hn : 1 ≤ n)
    (f h : ComplexVector n → ℂ) (θ : ComplexVector n → ComplexVector n)
    (φ : ComplexVector n → ℝ) (p : ℕ → ComplexVector n → ℝ)
    (R : ℝ) (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball 0 R))
    (hh : Differentiable ℂ h) (hθ : ContDiffOn ℝ 1 θ (ball 0 R)) (hθ0 : θ 0 = 0)
    (hθNZ : ∀ z ∈ ball (0 : ComplexVector n) R, z ≠ 0 → θ z ≠ 0)
    (hφ : ContinuousOn φ (ball 0 R)) (c : ℝ)
    (hp : ∀ j : ℕ, ∀ z ∈ ball (0 : ComplexVector n) R,
      p j z = ((n + 1 : ℕ) : ℝ) * Real.log (‖θ z‖ ^ 2 + poleEpsilon j) - c)
    (B : ℝ) (hb : ∀ j : ℕ,
      (∫⁻ z, ENNReal.ofReal (‖f z - h z‖ ^ 2 * Real.exp (-(φ z + p j z)))
        ∂(volume : Measure (ComplexVector n))) ≤ ENNReal.ofReal B) :
    h 0 = f 0 ∧ fderiv ℂ h 0 = fderiv ℂ f 0 := by
  let v : ComplexVector n → ℂ := fun z => f z - h z
  have hv : DifferentiableOn ℂ v (ball 0 R) := hf.sub hh.differentiableOn
  have hvm : AEStronglyMeasurable v
      ((volume : Measure (ComplexVector n)).restrict (ball 0 R)) :=
    hv.continuousOn.aestronglyMeasurable measurableSet_ball
  have hbase : ContinuousOn (fun z => φ z - c) (ball 0 R) := hφ.sub continuousOn_const
  have hvb (j : ℕ) : (∫⁻ z in ball (0 : ComplexVector n) R,
      ENNReal.ofReal (‖v z‖ ^ 2 * Real.exp (-(φ z - c)) *
        Real.exp (-((n + 1 : ℕ) : ℝ) * Real.log (‖θ z‖ ^ 2 + poleEpsilon j)))) ≤
          ENNReal.ofReal B := by
    calc
      _ = ∫⁻ z in ball (0 : ComplexVector n) R,
          ENNReal.ofReal (‖f z - h z‖ ^ 2 * Real.exp (-(φ z + p j z))) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        rw [hp j z hz]
        change ENNReal.ofReal (‖v z‖ ^ 2 * Real.exp (-(φ z - c)) *
            Real.exp (-((n + 1 : ℕ) : ℝ) * Real.log (‖θ z‖ ^ 2 + poleEpsilon j))) =
          ENNReal.ofReal (‖v z‖ ^ 2 * Real.exp (-(φ z +
            (((n + 1 : ℕ) : ℝ) * Real.log (‖θ z‖ ^ 2 + poleEpsilon j) - c))))
        congr 1
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring
      _ ≤ ∫⁻ z, ENNReal.ofReal (‖f z - h z‖ ^ 2 * Real.exp (-(φ z + p j z))) :=
        setLIntegral_le_lintegral _ _
      _ ≤ _ := hb j
  obtain ⟨r, hr, hrR, hfinite⟩ := PoleLimit.finite_critical_norm_of_coordinate_poles
    v θ (fun z => φ z - c) R hR hθ hθ0 hθNZ hbase hvm B hvb
  obtain ⟨hv0, hvc, _⟩ := PoleJets.critical_pole_jets_zero hn v r hr
    (hv.mono (ball_subset_ball hrR.le)) hfinite
  change f 0 - h 0 = 0 at hv0
  have hf0 : DifferentiableAt ℂ f 0 :=
    (hf 0 (mem_ball_self hR)).differentiableAt (ball_mem_nhds 0 hR)
  change fderiv ℂ (f - h) 0 = 0 at hvc
  rw [fderiv_sub hf0 (hh 0)] at hvc
  exact ⟨(sub_eq_zero.mp hv0).symm, (sub_eq_zero.mp hvc).symm⟩

end Yau.Proofs.C03Aux.CorrectionJets
