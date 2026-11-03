import Yau.LeafProofs.L23LocalDistanceSupport

/-! Compact spatial buffers and the length cost of reaching their boundary. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

def fieldDistanceBuffer (h : HermitianField M) (p : M.Carrier) (rIn rOut : ℝ) :
    Set M.Carrier := {y | inducedDistance h p y ≤ (rIn+rOut)/2}

theorem fieldDistanceBuffer_subset_outerBall (h : HermitianField M)
    (p : M.Carrier) {rIn rOut : ℝ} (hIn : 0 < rIn) (hInOut : rIn < rOut) :
    fieldDistanceBuffer h p rIn rOut ⊆ distBall h p rOut := by
  intro y hy
  apply (mem_distBall_iff h p y (hIn.trans hInOut)).mpr
  exact hy.trans_lt (by linarith)

theorem fieldDistanceBuffer_isCompact (h : HermitianField M) (hh : MetricSmooth h)
    (p : M.Carrier) {rIn rOut rBound : ℝ}
    (hIn : 0 < rIn) (hInOut : rIn < rOut) (hOut : rOut ≤ rBound)
    (hcO : IsCompact (closure (distBall h p rBound))) :
    IsCompact (fieldDistanceBuffer h p rIn rOut) := by
  have hclosed : IsClosed (fieldDistanceBuffer h p rIn rOut) :=
    isClosed_le (continuous_distFrom h hh p) continuous_const
  apply hcO.of_isClosed_subset hclosed
  intro y hy
  apply subset_closure
  apply (mem_distBall_iff h p y ((hIn.trans hInOut).trans_le hOut)).mpr
  exact (show inducedDistance h p y ≤ (rIn+rOut)/2 from hy).trans_lt (by linarith)

theorem innerBall_subset_fieldDistanceBuffer (h : HermitianField M)
    (p : M.Carrier) {rIn rOut : ℝ} (hIn : 0 < rIn) (hInOut : rIn < rOut) :
    distBall h p rIn ⊆ fieldDistanceBuffer h p rIn rOut := by
  intro q hq
  have H := (mem_distBall_iff h p q hIn).mp hq
  change inducedDistance h p q ≤ (rIn+rOut)/2
  linarith

theorem initial_buffer_boundary_distance (h : HermitianField M) (hh : MetricSmooth h)
    (p q y : M.Carrier) {rIn rOut : ℝ} (hIn : 0 < rIn)
    (hq : q ∈ distBall h p rIn)
    (hy : inducedDistance h p y = (rIn+rOut)/2) :
    (rOut-rIn)/2 < inducedDistance h q y := by
  have hq' := (mem_distBall_iff h p q hIn).mp hq
  have htri := inducedDistance_triangle h hh p q y
  linarith

theorem curveSpeed_lower_of_tangentNorm_lower
    (h₀ h₁ : HermitianField M) (O : Set M.Carrier) (ell : ℝ) (hell : 0 ≤ ell)
    (hmetric : ∀ x ∈ O, ∀ v : TangentVector M x,
      ell^2*(2*hermitianNormSq (h₀ x) v) ≤ 2*hermitianNormSq (h₁ x) v)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) {s : ℝ} (hs : γ s ∈ O) :
    ell*curveSpeed h₀ γ s ≤ curveSpeed h₁ γ s := by
  have H := Real.sqrt_le_sqrt (hmetric (γ s) hs (realTangentDerivative γ s))
  rw [Real.sqrt_mul (sq_nonneg ell), Real.sqrt_sq hell] at H
  exact H

theorem curveLength_lower_of_tangentNorm_lower
    (h₀ h₁ : HermitianField M) (O : Set M.Carrier) (ell : ℝ) (hell : 0 ≤ ell)
    (hmetric : ∀ x ∈ O, ∀ v : TangentVector M x,
      ell^2*(2*hermitianNormSq (h₀ x) v) ≤ 2*hermitianNormSq (h₁ x) v)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y)
    (hγ₀ : IntegrableOn (curveSpeed h₀ γ) (Set.Icc (0 : ℝ) 1))
    (hγ₁ : IntegrableOn (curveSpeed h₁ γ) (Set.Icc (0 : ℝ) 1))
    (himage : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ O) :
    ell*curveLength h₀ γ ≤ curveLength h₁ γ := by
  unfold curveLength
  rw [← integral_const_mul]
  exact setIntegral_mono_on (hγ₀.const_mul ell) hγ₁ measurableSet_Icc
    (fun s hs => curveSpeed_lower_of_tangentNorm_lower h₀ h₁ O ell hell hmetric γ (himage s hs))

/-- Once the initial segment reaches the fixed middle sphere while remaining
in the controlled open set, its length exceeds the escape budget. -/
theorem curveLength_gt_buffer_escape_budget
    (h₀ h₁ : HermitianField M) (hh₀ : MetricSmooth h₀)
    (O : Set M.Carrier) (p q y : M.Carrier) {rIn rOut ell : ℝ}
    (hIn : 0 < rIn) (hell : 0 < ell)
    (hq : q ∈ distBall h₀ p rIn)
    (hy : inducedDistance h₀ p y = (rIn+rOut)/2)
    (hmetric : ∀ x ∈ O, ∀ v : TangentVector M x,
      ell^2*(2*hermitianNormSq (h₀ x) v) ≤ 2*hermitianNormSq (h₁ x) v)
    (γ : IntegrableCurve h₀ q y)
    (hγ₁ : IntegrableOn (curveSpeed h₁ γ.1) (Set.Icc (0 : ℝ) 1))
    (himage : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ.1 s ∈ O) :
    ell*(rOut-rIn)/2 < curveLength h₁ γ.1 := by
  have hdist := initial_buffer_boundary_distance h₀ hh₀ p q y hIn hq hy
  have hlen := inducedDistance_le_curveLength h₀ γ
  have hcomp := curveLength_lower_of_tangentNorm_lower h₀ h₁ O ell hell.le hmetric γ.1 γ.2 hγ₁ himage
  have H := mul_lt_mul_of_pos_left (hdist.trans_le hlen) hell
  calc
    ell*(rOut-rIn)/2 = ell*((rOut-rIn)/2) := by ring
    _ < ell*curveLength h₀ γ.1 := H
    _ ≤ curveLength h₁ γ.1 := hcomp

end Yau.LeafProofs.L23Aux
