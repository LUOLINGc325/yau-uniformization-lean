import spec.CHAIN.CONTRACTS

/-! The actual scalar penalty used in the largest-eigenvalue maximum
principle, with its first and second derivatives on the whole relevant range. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux

def rayleighPenalty (a v : ℝ) : ℝ := a * v + Real.log (1 + a * v)

theorem rayleighPenalty_hasDerivAt (a v : ℝ) (hv : 1 + a * v ≠ 0) :
    HasDerivAt (rayleighPenalty a) (a + a / (1 + a * v)) v := by
  have hlinear : HasDerivAt (fun w : ℝ => 1 + a * w) a v := by
    convert (hasDerivAt_id v).const_mul a |>.const_add 1 using 1 <;> simp
  have hmul : HasDerivAt (fun w : ℝ => a * w) a v := by
    convert (hasDerivAt_id v).const_mul a using 1 <;> simp
  exact hmul.add (hlinear.log hv)

theorem rayleighPenalty_deriv (a v : ℝ) (hv : 1 + a * v ≠ 0) :
    deriv (rayleighPenalty a) v = a + a / (1 + a * v) :=
  (rayleighPenalty_hasDerivAt a v hv).deriv

theorem rayleighPenalty_deriv_hasDerivAt (a v : ℝ) (hv : 1 + a * v ≠ 0) :
    HasDerivAt (deriv (rayleighPenalty a)) (-(a ^ 2) / (1 + a * v) ^ 2) v := by
  have hlinear : HasDerivAt (fun w : ℝ => 1 + a * w) a v := by
    convert (hasDerivAt_id v).const_mul a |>.const_add 1 using 1 <;> simp
  have hh := ((hasDerivAt_const v a).div hlinear hv).const_add a
  have hopen : IsOpen {w : ℝ | 1 + a * w ≠ 0} :=
    isOpen_ne.preimage (continuous_const.add (continuous_const.mul continuous_id))
  have hgerm : deriv (rayleighPenalty a) =ᶠ[nhds v]
      (fun w => a + a / (1 + a * w)) := by
    filter_upwards [hopen.mem_nhds hv] with w hw
    exact rayleighPenalty_deriv a w hw
  apply (hh.congr_of_eventuallyEq hgerm).congr_deriv
  ring

theorem rayleighPenalty_second_deriv (a v : ℝ) (hv : 1 + a * v ≠ 0) :
    deriv (deriv (rayleighPenalty a)) v = -(a ^ 2) / (1 + a * v) ^ 2 :=
  (rayleighPenalty_deriv_hasDerivAt a v hv).deriv

theorem rayleighPenalty_nonneg {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) :
    0 ≤ rayleighPenalty a v := by
  exact add_nonneg (mul_nonneg ha hv) (Real.log_nonneg (by nlinarith))

theorem rayleighPenalty_deriv_bounds {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) :
    a ≤ deriv (rayleighPenalty a) v ∧ deriv (rayleighPenalty a) v ≤ 2 * a := by
  have hd : 0 < 1 + a * v := by positivity
  rw [rayleighPenalty_deriv a v hd.ne']
  have hratio : a / (1 + a * v) ≤ a :=
    (div_le_iff₀ hd).mpr (by nlinarith [mul_nonneg ha hv])
  constructor
  · exact le_add_of_nonneg_right (div_nonneg ha hd.le)
  · linarith

theorem rayleighPenalty_exp {a v : ℝ} (hv : 0 < 1 + a * v) :
    Real.exp (rayleighPenalty a v) = Real.exp (a * v) * (1 + a * v) := by
  rw [rayleighPenalty, Real.exp_add, Real.exp_log hv]

theorem rayleighPenalty_contact_lower {a v W : ℝ}
    (ha : 0 ≤ a) (hv : 0 ≤ v) (hW : Real.exp (rayleighPenalty a v) ≤ W) :
    1 + a * v ≤ W := by
  have hd : 0 < 1 + a * v := by positivity
  rw [rayleighPenalty_exp hd] at hW
  have he : 1 ≤ Real.exp (a * v) := Real.one_le_exp (mul_nonneg ha hv)
  nlinarith

end Yau.NodeProofs.F01Aux
