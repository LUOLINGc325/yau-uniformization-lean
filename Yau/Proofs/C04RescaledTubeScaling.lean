import Yau.Proofs.C04Scaling
import Yau.Proofs.C04FieldSmooth
import Yau.LeafProofs.L23FieldMetric

/-! Constant positive rescaling of the actual field and its length distance. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realMetricFn_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (x : M.Carrier) (z : ComplexVector n) :
    realMetricFn (scaleField c hc k) x z = c • realMetricFn k x z := by
  ext a b
  simp only [realMetricFn, scaleField, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Matrix.smul_apply, smul_eq_mul]
  ring

theorem metricSmooth_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hk : MetricSmooth k) : MetricSmooth (scaleField c hc k) := by
  intro x a b
  simp only [realMetricFn_scale, Matrix.smul_apply, smul_eq_mul]
  exact contDiffOn_const.mul (hk x a b)

theorem kahlerFormFn_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (x : M.Carrier) (z : ComplexVector n) (a b : RIdx n) :
    kahlerFormFn (scaleField c hc k) x z a b = c * kahlerFormFn k x z a b := by
  simp only [kahlerFormFn, scaleField, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  ring

theorem kahlerFormFn_differentiableAt (k : HermitianField M) (hk : MetricSmooth k)
    (x : M.Carrier) (a b : RIdx n) :
    DifferentiableAt ℝ (fun z => kahlerFormFn k x z a b) (chartPt x x) := by
  simp_rw [LeafProofs.L12Aux.kahlerFormFn_eq_jIndex_metric]
  exact (((hk x (jIndex n a) b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
        (mem_extChartAt_target x))).differentiableAt (by simp)).const_mul _

theorem kahlerClosed_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hs : MetricSmooth k) (hk : KahlerClosed k) : KahlerClosed (scaleField c hc k) := by
  intro x a b d
  simp only [kahlerFormFn_scale]
  rw [LeafProofs.L12Aux.rDeriv_const_mul (kahlerFormFn_differentiableAt k hs x b d),
    LeafProofs.L12Aux.rDeriv_const_mul (kahlerFormFn_differentiableAt k hs x d a),
    LeafProofs.L12Aux.rDeriv_const_mul (kahlerFormFn_differentiableAt k hs x a b)]
  have hh := hk x a b d
  nlinarith

theorem curveSpeed_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) (t : ℝ) :
    curveSpeed (scaleField c hc k) γ t = Real.sqrt c * curveSpeed k γ t := by
  simp only [curveSpeed, hermitianNormSq, scaleField, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  let Q := ((k (γ t)).toFun (realTangentDerivative γ t) (realTangentDerivative γ t)).re
  change Real.sqrt (2 * (c * Q)) = Real.sqrt c * Real.sqrt (2 * Q)
  rw [show 2 * (c * Q) = c * (2 * Q) by ring, Real.sqrt_mul hc.le]

theorem integrableCurve_scale_iff (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) :
    IntegrableOn (curveSpeed (scaleField c hc k) γ) (Set.Icc (0 : ℝ) 1) ↔
      IntegrableOn (curveSpeed k γ) (Set.Icc (0 : ℝ) 1) := by
  change IntegrableOn (fun t => curveSpeed (scaleField c hc k) γ t) _ ↔ _
  simp_rw [curveSpeed_scale]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.2 (Real.sqrt_pos.2 hc).ne') _

theorem curveLength_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) :
    curveLength (scaleField c hc k) γ = Real.sqrt c * curveLength k γ := by
  simp only [curveLength, curveSpeed_scale, integral_const_mul]

theorem distance_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hk : MetricSmooth k) (x y : M.Carrier) :
    inducedDistance (scaleField c hc k) x y = Real.sqrt c * inducedDistance k x y := by
  let q := scaleField c hc k
  have hq := metricSmooth_scale c hc k hk
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hbelow (f : HermitianField M) :
      BddBelow (Set.range (fun γ : IntegrableCurve f x y => curveLength f γ.1)) :=
    ⟨0, by rintro _ ⟨γ, rfl⟩; exact LeafProofs.L12Aux.curveLength_nonneg f γ.1⟩
  have hne (f : HermitianField M) (hf : MetricSmooth f) :
      (Set.range (fun γ : IntegrableCurve f x y => curveLength f γ.1)).Nonempty := by
    obtain ⟨γ⟩ := LeafProofs.L23Aux.integrable_curve_nonempty f hf x y
    exact ⟨_, Set.mem_range_self γ⟩
  apply le_antisymm
  · have hd : inducedDistance q x y / Real.sqrt c ≤ inducedDistance k x y := by
      apply le_csInf (hne k hk)
      rintro _ ⟨γ, rfl⟩
      apply (div_le_iff₀ hs).2
      let η : IntegrableCurve q x y := ⟨γ.1, (integrableCurve_scale_iff c hc k γ.1).2 γ.2⟩
      have hb := csInf_le (hbelow q) (Set.mem_range_self η)
      change inducedDistance q x y ≤ curveLength q γ.1 at hb
      simpa only [q, curveLength_scale, mul_comm] using hb
    exact (div_le_iff₀ hs).1 hd |>.trans_eq (mul_comm _ _)
  · apply le_csInf (hne q hq)
    rintro _ ⟨γ, rfl⟩
    let η : IntegrableCurve k x y := ⟨γ.1, (integrableCurve_scale_iff c hc k γ.1).1 γ.2⟩
    have hb := csInf_le (hbelow k) (Set.mem_range_self η)
    change inducedDistance k x y ≤ curveLength k γ.1 at hb
    simpa only [q, curveLength_scale] using mul_le_mul_of_nonneg_left hb hs.le

theorem complete_scale (c : ℝ) (hc : 0 < c) (k : HermitianField M)
    (hk : MetricSmooth k) (hcomplete : IsCompleteDistance (lengthDist k)) :
    IsCompleteDistance (lengthDist (scaleField c hc k)) := by
  intro s hs
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hC : IsCauchy (lengthDist k) s := by
    intro ε hε
    obtain ⟨N, hN⟩ := hs (Real.sqrt c * ε) (mul_pos hsq hε)
    refine ⟨N, fun j l hj hl => ?_⟩
    have hb := hN j l hj hl
    change inducedDistance (scaleField c hc k) (s j) (s l) < Real.sqrt c * ε at hb
    rw [distance_scale c hc k hk] at hb
    exact (mul_lt_mul_iff_right₀ hsq).1 hb
  obtain ⟨x, hx⟩ := hcomplete s hC
  refine ⟨x, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hx (ε / Real.sqrt c) (div_pos hε hsq)
  refine ⟨N, fun j hj => ?_⟩
  change inducedDistance (scaleField c hc k) (s j) x < ε
  rw [distance_scale c hc k hk]
  simpa only [mul_comm] using (lt_div_iff₀ hsq).1 (hN j hj)

end Yau.Proofs.C04RescaledTubeAux
