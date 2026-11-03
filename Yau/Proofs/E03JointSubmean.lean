import Yau.Proofs.E03EnvelopeRigidity
import Yau.Proofs.E03AffineDiscs

/-! Original raw-envelope competitors imply the genuine affine joint submean inequality. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
variable {n : ℕ} {X : KahlerManifold n}

theorem jointNorm_affine_submean (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (hcomp : EllipsoidComparison X h) (hscalar : ScalarComparison X h ρ)
    (c : Pt X) (p v : JointSpace n)
    (hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → p + ζ • v ∈ jointDomain c) :
    jointNorm h c p ≤ circleAverage (fun θ : ℝ => jointNorm h c (p + Complex.exp (θ * Complex.I) • v)) := by
  let time : ℂ → ℝ := fun ζ => Real.exp (2 * (p.2.2 + ζ * v.2.2).re)
  have htime : Continuous time := Real.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_re.comp (continuous_const.add (continuous_id.mul continuous_const))))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1 |>.image htime).bddAbove
  have hbound (ζ : ℂ) (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) : time ζ ≤ C :=
    hC ⟨ζ, hζ, rfl⟩
  let t : ℝ := Real.exp (2 * p.2.2.re)
  let T : ℝ := C + 1
  have ht : 0 < t := Real.exp_pos _
  have htT : t < T := by
    have hb := hbound 0 (by simp)
    simpa only [time, zero_mul, add_zero] using hb.trans_lt (lt_add_one C)
  have hT : 0 < T := ht.trans htT
  let f : ℂ → Pt X := fun ζ => chartInv c (p.1 + ζ • v.1)
  let ξd : ℂ → Covector n := fun ζ =>
    covectorOfCoords c (f ζ) (p.2.1 + ζ • v.2.1)
  let w : ℂ → ℂ := fun ζ => ζ * v.2.2
  have hbase (ζ : ℂ) (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
      p.1 + ζ • v.1 ∈ chartTarget c := by
    exact hdisc ζ (by simpa only [Metric.mem_closedBall, dist_zero_right] using hζ)
  have htformula (ζ : ℂ) : t * Real.exp (2 * (w ζ).re) = time ζ := by
    simp only [t, time, w, Complex.add_re, mul_add, Real.exp_add]
  have had : 0 < t ∧ t < T ∧ IsCotangentDisc f ξd ∧
      ContDiffOn ℂ ∞ w (Metric.closedBall 0 1) ∧ f 0 = f 0 ∧ ξd 0 = ξd 0 ∧
      w 0 = 0 ∧ ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, t * Real.exp (2 * (w ζ).re) < T := by
    refine ⟨ht, htT, chart_affine_isCotangentDisc c _ _ _ _ hbase,
      (contDiff_id.mul contDiff_const).contDiffOn, rfl, rfl, ?_, ?_⟩
    · exact zero_mul _
    · intro ζ hζ
      rw [htformula]
      exact (hbound ζ hζ).trans_lt (lt_add_one C)
  have hr : envelopeRaw h T (f 0) (ξd 0) t ≤
      (circleAverage (fun θ => dualNorm (h (t * Real.exp (2 * (w (Complex.exp (θ * Complex.I))).re)))
        (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))) : EReal) := by
    unfold envelopeRaw
    exact iInf_le_of_le f (iInf_le_of_le ξd (iInf_le_of_le w (iInf_le_of_le had le_rfl)))
  rw [envelopeRaw_eq_dualNorm o h U P ρ hloc hopt hcomp hscalar T hT (f 0) (ξd 0) t ht htT] at hr
  have hnorm (ζ : ℂ) (hζ : ζ ∈ Metric.closedBall (0 : ℂ) 1) :
      dualNorm (h (t * Real.exp (2 * (w ζ).re))) (f ζ) (ξd ζ) = jointNorm h c (p + ζ • v) := by
    rw [htformula]
    exact dualNorm_cotangentChartInv (h (time ζ)) c
      (z := (p.1 + ζ • v.1, p.2.1 + ζ • v.2.1)) ⟨hbase ζ hζ, mem_univ _⟩
  have havg : (fun θ : ℝ => dualNorm (h (t * Real.exp (2 * (w (Complex.exp (θ * Complex.I))).re)))
        (f (Complex.exp (θ * Complex.I))) (ξd (Complex.exp (θ * Complex.I)))) =
      (fun θ : ℝ => jointNorm h c (p + Complex.exp (θ * Complex.I) • v)) := by
    funext θ
    apply hnorm
    simp [Metric.mem_closedBall, Complex.norm_exp, Complex.mul_re]
  rw [havg] at hr
  have hcenter := hnorm 0 (by simp)
  simp only [w, zero_mul, Complex.zero_re, mul_zero, Real.exp_zero, mul_one,
    zero_smul, add_zero] at hcenter
  rw [hcenter] at hr
  exact EReal.coe_le_coe_iff.mp hr

end Yau.NodeProofs.E03Aux
