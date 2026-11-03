import Yau.LeafProofs.L16NormalHeatProfile

open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux

/-- The normal derivative of the actual Poisson kernel. -/
theorem normalPoissonKernel_hasDerivAt {r : ℝ} (hr : 0 < r) (a : ℝ) :
    HasDerivAt (fun b => normalPoissonKernel b r)
      ((1/r-a^2/(2*r^2))*normalGaussianKernel r a) a := by
  convert ((hasDerivAt_id a).div_const r).mul (normalGaussianKernel_hasDerivAt r a) using 1
  · rfl
  · dsimp only [id_eq]
    field_simp
    ring

private theorem normalPoissonKernel_weight_formula {r : ℝ} (hr : 0 < r) (a q : ℝ) :
    normalPoissonKernel a r * r^q =
      (a*(Real.sqrt (4*Real.pi))⁻¹) *
        (r^(q-3/2)*Real.exp (-(a^2/4)*r⁻¹)) := by
  rw [normalPoissonKernel,normalGaussianKernel,Real.sqrt_mul (by positivity : 0 ≤ 4*Real.pi),
    mul_inv_rev]
  have hPow : r⁻¹*((Real.sqrt r)⁻¹*r^q) = r^(q-3/2) := by
    rw [← Real.rpow_neg_one r,Real.sqrt_eq_rpow,← Real.rpow_neg hr.le,← Real.rpow_add hr,← Real.rpow_add hr]
    congr 1
    ring
  have hExp : -(4*r)⁻¹*a^2 = -(a^2/4)*r⁻¹ := by ring_nf
  rw [hExp]
  rw [div_eq_mul_inv]
  calc
    _ = (a*(Real.sqrt (4*Real.pi))⁻¹)*
        (r⁻¹*((Real.sqrt r)⁻¹*r^q))*Real.exp (-(a^2/4)*r⁻¹) := by ring
    _ = _ := by rw [hPow]; ring

private theorem integrableOn_rpow_exp_neg_inv {u b : ℝ} (hu : u < -1) (hb : 0 < b) :
    IntegrableOn (fun r : ℝ => r^u*Real.exp (-b*r⁻¹)) (Set.Ioi 0) := by
  apply (integrableOn_Ioi_comp_rpow_iff' _ (by norm_num : (-1 : ℝ) ≠ 0)).mp
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < -2-u)
    (by norm_num : (0 : ℝ) < 1) hb
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [smul_eq_mul,Real.rpow_one]
  rw [← Real.rpow_mul hx.le,← mul_assoc,← Real.rpow_add hx]
  norm_num [Real.rpow_neg_one,sub_eq_add_neg]

/-- All unit normal Poisson moments below order one are integrable. -/
theorem normalPoissonKernel_unit_weight_integrable {q : ℝ} (hq : q < 1/2) :
    IntegrableOn (fun r => normalPoissonKernel 1 r*r^q) (Set.Ioi 0) := by
  have h := (integrableOn_rpow_exp_neg_inv (by linarith : q-3/2 < -1)
    (by norm_num : (0 : ℝ) < 1^2/4)).const_mul (1*(Real.sqrt (4*Real.pi))⁻¹)
  exact IntegrableOn.congr_fun h (fun r hr => (normalPoissonKernel_weight_formula hr 1 q).symm) measurableSet_Ioi

/-- Scaling the time variable by the square of the normal coordinate. -/
theorem normalPoissonKernel_time_scaling {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    a^2*normalPoissonKernel a (a^2*r) = normalPoissonKernel 1 r := by
  have hs : Real.sqrt (4*Real.pi*(a^2*r)) = a*Real.sqrt (4*Real.pi*r) := by
    rw [show 4*Real.pi*(a^2*r) = a^2*(4*Real.pi*r) by ring,
      Real.sqrt_mul (sq_nonneg a),Real.sqrt_sq ha.le]
  have he : -(4*(a^2*r))⁻¹*a^2 = -(4*r)⁻¹*1^2 := by field_simp
  dsimp only [normalPoissonKernel,normalGaussianKernel]
  rw [hs,he]
  field_simp

private theorem normalPoissonKernel_weight_scaling {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (q : ℝ) :
    a^2*(normalPoissonKernel a (a^2*r)*(a^2*r)^q) =
      a^(2*q)*(normalPoissonKernel 1 r*r^q) := by
  rw [Real.mul_rpow (sq_nonneg a) hr.le]
  rw [show (a^2)^q = a^(2*q) by rw [Real.rpow_mul ha.le,Real.rpow_two]]
  calc
    _ = (a^2*normalPoissonKernel a (a^2*r))*(a^(2*q)*r^q) := by ring
    _ = _ := by rw [normalPoissonKernel_time_scaling ha hr]; ring

/-- Weighted Poisson integrability for every exponent less than one half. -/
theorem normalPoissonKernel_weight_integrable {q a : ℝ} (hq : q < 1/2) (ha : 0 < a) :
    IntegrableOn (fun r => normalPoissonKernel a r*r^q) (Set.Ioi 0) := by
  have h := ((normalPoissonKernel_unit_weight_integrable hq).const_mul
    (a^(2*q))).const_mul ((a^2)⁻¹)
  have hc : IntegrableOn (fun r => normalPoissonKernel a (a^2*r)*(a^2*r)^q)
      (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun h (fun r hr => ?_) measurableSet_Ioi
    rw [← normalPoissonKernel_weight_scaling ha hr q]
    field_simp
  have ht := (integrableOn_Ioi_comp_mul_left_iff
    (fun r => normalPoissonKernel a r*r^q) 0 (sq_pos_of_pos ha)).mp hc
  simpa only [mul_zero] using ht

/-- The exact scaling of every integrable weighted Poisson moment. -/
theorem normalPoissonKernel_weight_integral {q a : ℝ} (hq : q < 1/2) (ha : 0 < a) :
    (∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*r^q) =
      a^(2*q)*(∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^q) := by
  have hInt := normalPoissonKernel_weight_integrable hq ha
  have hUnit := normalPoissonKernel_unit_weight_integrable hq
  have hChange := integral_comp_mul_left_Ioi'
    (fun r => normalPoissonKernel a r*r^q) 0 (sq_pos_of_pos ha)
  simp only [mul_zero,smul_eq_mul] at hChange
  rw [← hChange,← integral_const_mul]
  calc
    (∫ r in Set.Ioi (0 : ℝ), a^2*(normalPoissonKernel a (a^2*r)*(a^2*r)^q)) =
        ∫ r in Set.Ioi (0 : ℝ), a^(2*q)*(normalPoissonKernel 1 r*r^q) := by
      exact setIntegral_congr_fun measurableSet_Ioi (fun r hr =>
        normalPoissonKernel_weight_scaling ha hr q)
    _ = _ := integral_const_mul _ _

private theorem normalPoissonKernel_deriv_weight_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (q : ℝ) :
    |deriv (fun b => normalPoissonKernel b r) a| *r^q =
      |a⁻¹*(normalPoissonKernel a r*r^q) -
        (a/2)*(normalPoissonKernel a r*r^(q-1))| := by
  rw [(normalPoissonKernel_hasDerivAt hr a).deriv]
  calc
    _ = |((1/r-a^2/(2*r^2))*normalGaussianKernel r a)*r^q| := by
      simp only [abs_mul,abs_of_pos (Real.rpow_pos_of_pos hr q)]
    _ = _ := by
      congr 1
      rw [Real.rpow_sub hr,Real.rpow_one]
      simp only [normalPoissonKernel]
      field_simp

/-- The weighted absolute derivative is an honest integrable function. -/
theorem normalPoissonKernel_deriv_weight_integrable {q a : ℝ} (hq : q < 1/2) (ha : 0 < a) :
    IntegrableOn (fun r => |deriv (fun b => normalPoissonKernel b r) a| *r^q)
      (Set.Ioi 0) := by
  have h := ((normalPoissonKernel_weight_integrable hq ha).const_mul a⁻¹).sub
    ((normalPoissonKernel_weight_integrable (by linarith : q-1 < 1/2) ha).const_mul (a/2))
  exact IntegrableOn.congr_fun h.abs (fun r hr =>
    (normalPoissonKernel_deriv_weight_eq ha hr q).symm) measurableSet_Ioi

/-- A quantitative derivative moment bound in terms of two finite unit moments. -/
theorem normalPoissonKernel_deriv_weight_integral_le {q a : ℝ}
    (hq : q < 1/2) (ha : 0 < a) :
    (∫ r in Set.Ioi (0 : ℝ), |deriv (fun b => normalPoissonKernel b r) a| *r^q) ≤
      a^(2*q-1)*((∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^q) +
        (1/2)*(∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^(q-1))) := by
  have hq' : q-1 < 1/2 := by linarith
  have hi := normalPoissonKernel_weight_integrable hq ha
  have hj := normalPoissonKernel_weight_integrable hq' ha
  have hbound : (∫ r in Set.Ioi (0 : ℝ),
      |deriv (fun b => normalPoissonKernel b r) a| *r^q) ≤
      ∫ r in Set.Ioi (0 : ℝ),
        a⁻¹*(normalPoissonKernel a r*r^q)+(a/2)*(normalPoissonKernel a r*r^(q-1)) := by
    apply integral_mono_ae (normalPoissonKernel_deriv_weight_integrable hq ha)
      ((hi.const_mul a⁻¹).add (hj.const_mul (a/2)))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [normalPoissonKernel_deriv_weight_eq ha hr]
    have hx : 0 ≤ a⁻¹*(normalPoissonKernel a r*r^q) := by
      exact mul_nonneg (inv_nonneg.mpr ha.le)
        (mul_nonneg (normalPoissonKernel_nonneg ha.le hr) (Real.rpow_nonneg hr.le q))
    have hy : 0 ≤ (a/2)*(normalPoissonKernel a r*r^(q-1)) := by
      exact mul_nonneg (by positivity)
        (mul_nonneg (normalPoissonKernel_nonneg ha.le hr) (Real.rpow_nonneg hr.le _))
    exact (abs_sub _ _).trans_eq (by simp only [abs_of_nonneg hx,abs_of_nonneg hy,Pi.add_apply])
  rw [integral_add (hi.const_mul a⁻¹) (hj.const_mul (a/2)),integral_const_mul,
    integral_const_mul,normalPoissonKernel_weight_integral hq ha,
    normalPoissonKernel_weight_integral hq' ha] at hbound
  convert hbound using 1
  rw [Real.rpow_sub ha,Real.rpow_one,
    show 2*(q-1) = 2*q-2 by ring,Real.rpow_sub ha,Real.rpow_two]
  field_simp

/-- Uniform weighted bounds, with the constant chosen before the positive normal coordinate. -/
theorem normalPoissonKernel_weighted_moments {α : ℝ} (_hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a →
      IntegrableOn (fun r => normalPoissonKernel a r*r^(α/2)) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*r^(α/2)) ≤ C*a^α ∧
      IntegrableOn (fun r => |deriv (fun b => normalPoissonKernel b r) a| *r^(α/2))
        (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), |deriv (fun b => normalPoissonKernel b r) a| *r^(α/2)) ≤
        C*a^(α-1) := by
  let M : ℝ := ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^(α/2)
  let N : ℝ := ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^(α/2-1)
  have hq : α/2 < 1/2 := by linarith
  have hC : 0 < 1+|M|+|N| := by positivity
  have hMC : M ≤ 1+|M|+|N| := by linarith [le_abs_self M,abs_nonneg N]
  have hNC : M+(1/2)*N ≤ 1+|M|+|N| := by
    linarith [le_abs_self M,le_abs_self N,abs_nonneg N]
  refine ⟨1+|M|+|N|,hC,?_⟩
  intro a ha
  refine ⟨normalPoissonKernel_weight_integrable hq ha,?_,
    normalPoissonKernel_deriv_weight_integrable hq ha,?_⟩
  · rw [normalPoissonKernel_weight_integral hq ha,show 2*(α/2) = α by ring]
    change a^α*M ≤ (1+|M|+|N|)*a^α
    nlinarith [mul_le_mul_of_nonneg_left hMC (Real.rpow_nonneg ha.le α)]
  · have h := normalPoissonKernel_deriv_weight_integral_le hq ha
    rw [show 2*(α/2)-1 = α-1 by ring] at h
    change (∫ r in Set.Ioi (0 : ℝ), |deriv (fun b => normalPoissonKernel b r) a| *r^(α/2)) ≤
      a^(α-1)*(M+(1/2)*N) at h
    exact h.trans (by
      nlinarith [mul_le_mul_of_nonneg_left hNC (Real.rpow_nonneg ha.le (α-1))])

/-- Uniform fractional moments of the positive Poisson kernel. -/
theorem normalPoissonKernel_weighted_moment {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a →
      IntegrableOn (fun r => normalPoissonKernel a r*r^(α/2)) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*r^(α/2)) ≤ C*a^α := by
  obtain ⟨C,hC,h⟩ := normalPoissonKernel_weighted_moments hα0 hα1
  exact ⟨C,hC,fun a ha => ⟨(h a ha).1,(h a ha).2.1⟩⟩

/-- Uniform fractional moments of the genuine normal derivative of the Poisson kernel. -/
theorem normalPoissonKernel_deriv_weighted_moment {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a →
      IntegrableOn (fun r => |deriv (fun b => normalPoissonKernel b r) a| *r^(α/2))
        (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), |deriv (fun b => normalPoissonKernel b r) a| *r^(α/2)) ≤
        C*a^(α-1) := by
  obtain ⟨C,hC,h⟩ := normalPoissonKernel_weighted_moments hα0 hα1
  exact ⟨C,hC,fun a ha => (h a ha).2.2⟩

end Yau.LeafProofs.L16Aux
