import Yau.LeafProofs.L19EndpointEnergyBounds
import Yau.LeafProofs.L18

/-! Scalar composition of actual covariant Hessian traces and the positive
square-root profile used for the midpoint distance-square support. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal NNReal Matrix ContDiff Bundle ComplexOrder InnerProductSpace
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem endpointFrameGradientSq_scalar_comp
    (q : M.Carrier) (b : Fin (2 * n) → TangentSpace 𝓘(ℝ, ComplexVector n) q)
    {f : ComplexVector n → ℝ} {F : ℝ → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hF : DifferentiableAt ℝ F (f z)) :
    endpointFrameGradientSq q b (F ∘ f) z =
      deriv F (f z) ^ 2 * endpointFrameGradientSq q b f z := by
  rw [endpointFrameGradientSq, endpointFrameGradientSq, fderiv_comp z hF hf]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul, mul_pow]
  rw [Finset.mul_sum]

theorem endpointFrameHessianTrace_scalar_comp
    (g : SmoothMetric M) (q : M.Carrier)
    (b : Fin (2 * n) → TangentSpace 𝓘(ℝ, ComplexVector n) q)
    {f : ComplexVector n → ℝ} {F : ℝ → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hF : ContDiffAt ℝ 2 F (f z)) :
    endpointFrameHessianTrace g q b (F ∘ f) z =
      deriv F (f z) * endpointFrameHessianTrace g q b f z +
      deriv (deriv F) (f z) * endpointFrameGradientSq q b f z := by
  simp only [endpointFrameHessianTrace, endpointFrameGradientSq, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [secondFDeriv_comp hf hF, secondFDeriv_scalar_apply hF,
    fderiv_comp z (hF.differentiableAt (by simp)) (hf.differentiableAt (by simp))]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]
  ring

/-- This expanded profile equals `(a + sqrt x)^2` for nonnegative x,
and exposes the negative square-root second derivative. -/
def endpointDistanceSquareProfile (a x : ℝ) : ℝ :=
  a ^ 2 + 2 * a * Real.sqrt x + x

theorem endpointDistanceSquareProfile_eq {a x : ℝ} (hx : 0 ≤ x) :
    endpointDistanceSquareProfile a x = (a + Real.sqrt x) ^ 2 := by
  have hs := Real.sq_sqrt hx
  dsimp only [endpointDistanceSquareProfile]
  nlinarith

theorem endpointDistanceSquareProfile_contDiffAt {a x : ℝ} (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (endpointDistanceSquareProfile a) x :=
  (contDiffAt_const.add (contDiffAt_const.mul (Real.contDiffAt_sqrt hx))).add contDiffAt_id

theorem endpointDistanceSquareProfile_hasDerivAt {a x : ℝ} (hx : 0 < x) :
    HasDerivAt (endpointDistanceSquareProfile a) (a / Real.sqrt x + 1) x := by
  have hs := Real.hasDerivAt_sqrt hx.ne'
  have h := (((hs.const_mul (2 * a)).const_add (a ^ 2)).add (hasDerivAt_id x))
  convert h using 1
  · rfl
  · have hpos := Real.sqrt_pos.mpr hx
    field_simp
    <;> ring

theorem endpointDistanceSquareProfile_at_sq {a : ℝ} (ha : 0 < a) :
    endpointDistanceSquareProfile a (a ^ 2) = 4 * a ^ 2 := by
  rw [endpointDistanceSquareProfile_eq (sq_nonneg a), Real.sqrt_sq ha.le]
  ring

theorem endpointDistanceSquareProfile_deriv_at_sq {a : ℝ} (ha : 0 < a) :
    deriv (endpointDistanceSquareProfile a) (a ^ 2) = 2 := by
  rw [(endpointDistanceSquareProfile_hasDerivAt (sq_pos_of_pos ha)).deriv,
    Real.sqrt_sq ha.le, div_self ha.ne']
  norm_num

theorem endpointDistanceSquareProfile_secondDeriv_at_sq {a : ℝ} (ha : 0 < a) :
    deriv (deriv (endpointDistanceSquareProfile a)) (a ^ 2) = -(1 / (2 * a ^ 2)) := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * a)) (a ^ 2) := by
    simpa only [Real.sqrt_sq ha.le] using Real.hasDerivAt_sqrt (sq_pos_of_pos ha).ne'
  have hL := ((hasDerivAt_const (a ^ 2) a).div hs
    (by simpa only [Real.sqrt_sq ha.le] using ha.ne')).add_const 1
  have heq : deriv (endpointDistanceSquareProfile a) =ᶠ[𝓝 (a ^ 2)]
      (fun x => a / Real.sqrt x + 1) := by
    filter_upwards [Ioi_mem_nhds (sq_pos_of_pos ha)] with x hx
    exact (endpointDistanceSquareProfile_hasDerivAt hx).deriv
  simp only [Pi.div_apply] at hL
  rw [heq.deriv_eq, hL.deriv, Real.sqrt_sq ha.le]
  field_simp
  <;> ring

/-- The midpoint square-root profile doubles the energy derivative, and
its negative second derivative yields the required nonsharp trace bound. -/
theorem endpointDistanceSquareProfile_support_bounds
    (g : SmoothMetric M) (q : M.Carrier)
    (b : Fin (2 * n) → TangentSpace 𝓘(ℝ, ComplexVector n) q)
    {e : ComplexVector n → ℝ} {z : ComplexVector n} {a : ℝ}
    (ha : 0 < a) (he : ContDiffAt ℝ 2 e z) (hez : e z = a ^ 2)
    (hgrad : endpointFrameGradientSq q b e z = 4 * a ^ 2)
    (htrace : endpointFrameHessianTrace g q b e z ≤ 2 * (2 * n : ℕ)) :
    ContDiffAt ℝ 2 (endpointDistanceSquareProfile a ∘ e) z ∧
    (endpointDistanceSquareProfile a ∘ e) z = 4 * a ^ 2 ∧
    endpointFrameGradientSq q b (endpointDistanceSquareProfile a ∘ e) z = 16 * a ^ 2 ∧
    endpointFrameHessianTrace g q b (endpointDistanceSquareProfile a ∘ e) z ≤ 4 * (2 * n : ℕ) := by
  have hF : ContDiffAt ℝ 2 (endpointDistanceSquareProfile a) (e z) :=
    endpointDistanceSquareProfile_contDiffAt (hez ▸ (sq_pos_of_pos ha).ne')
  refine ⟨hF.comp z he, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, hez, endpointDistanceSquareProfile_at_sq ha]
  · rw [endpointFrameGradientSq_scalar_comp q b (he.differentiableAt (by simp))
      (hF.differentiableAt (by simp)), hez, endpointDistanceSquareProfile_deriv_at_sq ha, hgrad]
    ring
  · rw [endpointFrameHessianTrace_scalar_comp g q b he hF, hez,
      endpointDistanceSquareProfile_deriv_at_sq ha, endpointDistanceSquareProfile_secondDeriv_at_sq ha,
      hgrad]
    have hn : -(1 / (2 * a ^ 2)) * (4 * a ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
    linarith

end Yau.LeafProofs.L19Aux
