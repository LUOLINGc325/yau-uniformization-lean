import Yau.LeafProofs.L16NormalPoissonMoments

open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux

/-- The normal Gaussian decreases on the nonnegative half line. -/
theorem normalGaussianKernel_antitone_nonneg {r a ξ : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (haξ : a ≤ ξ) :
    normalGaussianKernel r ξ ≤ normalGaussianKernel r a := by
  have hξ : 0 ≤ ξ := ha.trans haξ
  have hsq : a^2 ≤ ξ^2 := by nlinarith [mul_le_mul haξ haξ ha hξ]
  dsimp only [normalGaussianKernel]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr (by positivity))

/-- An actual normal derivative majorant uniform between `a` and `2*a`. -/
theorem normalPoissonKernel_deriv_le_near {r a ξ : ℝ}
    (hr : 0 < r) (ha : 0 < a) (haξ : a ≤ ξ) (hξ : ξ ≤ 2*a) :
    |deriv (fun b => normalPoissonKernel b r) ξ| ≤
      a⁻¹*normalPoissonKernel a r + 2*a*normalPoissonKernel a r/r := by
  have hξ0 : 0 ≤ ξ := ha.le.trans haξ
  have hsq : ξ^2 ≤ 4*a^2 := by
    nlinarith [mul_le_mul hξ hξ hξ0 (by positivity : 0 ≤ 2*a)]
  have hfrac : ξ^2/(2*r^2) ≤ 2*a^2/r^2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*r^2)).2
    field_simp
    nlinarith
  have hc : |1/r-ξ^2/(2*r^2)| ≤ 1/r+2*a^2/r^2 := by
    calc
      _ ≤ |1/r|+|ξ^2/(2*r^2)| := abs_sub _ _
      _ = 1/r+ξ^2/(2*r^2) := by rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      _ ≤ _ := by linarith
  rw [(normalPoissonKernel_hasDerivAt hr ξ).deriv,abs_mul,
    abs_of_pos (normalGaussianKernel_pos hr ξ)]
  calc
    _ ≤ (1/r+2*a^2/r^2)*normalGaussianKernel r a :=
      mul_le_mul hc (normalGaussianKernel_antitone_nonneg hr ha.le haξ)
        (normalGaussianKernel_pos hr ξ).le (by positivity)
    _ = _ := by
      dsimp only [normalPoissonKernel]
      field_simp

/-- Mean value estimate for the actual Poisson kernels at two nearby heights. -/
theorem normalPoissonKernel_sub_le_near {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ 2*a) :
    |normalPoissonKernel b r-normalPoissonKernel a r| ≤
      (b-a)*(a⁻¹*normalPoissonKernel a r+2*a*normalPoissonKernel a r/r) := by
  have hMean := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun ξ (_hξ : ξ ∈ Set.Icc a b) => (normalPoissonKernel_hasDerivAt hr ξ).differentiableAt)
    (fun ξ (hξ : ξ ∈ Set.Icc a b) => by
      simpa only [Real.norm_eq_abs] using
        normalPoissonKernel_deriv_le_near hr ha hξ.1 (hξ.2.trans hba))
    (convex_Icc a b) (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using hMean

/-- The absolute weighted difference is integrable at any two positive heights. -/
theorem normalPoissonKernel_sub_weight_integrable {q a b : ℝ}
    (hq : q < 1/2) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun r => |normalPoissonKernel b r-normalPoissonKernel a r| *r^q)
      (Set.Ioi 0) := by
  have h := ((normalPoissonKernel_weight_integrable hq hb).sub
    (normalPoissonKernel_weight_integrable hq ha)).abs
  refine IntegrableOn.congr_fun h (fun r hr => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]
  rw [← sub_mul,abs_mul,abs_of_pos (Real.rpow_pos_of_pos hr q)]

/-- The nearby kernel difference is bounded by its two actual Poisson moments. -/
theorem normalPoissonKernel_sub_weight_integral_le_near {q a b : ℝ}
    (hq : q < 1/2) (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ 2*a) :
    (∫ r in Set.Ioi (0 : ℝ), |normalPoissonKernel b r-normalPoissonKernel a r| *r^q) ≤
      (b-a)*a^(2*q-1)*((∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^q)+
        2*(∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^(q-1))) := by
  have hq' : q-1 < 1/2 := by linarith
  have hi := normalPoissonKernel_weight_integrable hq ha
  have hj := normalPoissonKernel_weight_integrable hq' ha
  have hbound : (∫ r in Set.Ioi (0 : ℝ),
      |normalPoissonKernel b r-normalPoissonKernel a r| *r^q) ≤
      ∫ r in Set.Ioi (0 : ℝ), (b-a)*
        (a⁻¹*(normalPoissonKernel a r*r^q)+2*a*(normalPoissonKernel a r*r^(q-1))) := by
    apply integral_mono_ae (normalPoissonKernel_sub_weight_integrable hq ha (ha.trans_le hab))
      (((hi.const_mul a⁻¹).add (hj.const_mul (2*a))).const_mul (b-a))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    calc
      _ ≤ (b-a)*(a⁻¹*normalPoissonKernel a r+2*a*normalPoissonKernel a r/r)*r^q :=
        mul_le_mul_of_nonneg_right (normalPoissonKernel_sub_le_near hr ha hab hba)
          (Real.rpow_nonneg hr.le q)
      _ = _ := by
        simp only [Pi.add_apply]
        rw [Real.rpow_sub hr,Real.rpow_one]
        field_simp
  rw [integral_const_mul,integral_add (hi.const_mul a⁻¹) (hj.const_mul (2*a)),
    integral_const_mul,integral_const_mul,normalPoissonKernel_weight_integral hq ha,
    normalPoissonKernel_weight_integral hq' ha] at hbound
  convert hbound using 1
  rw [Real.rpow_sub ha,Real.rpow_one,
    show 2*(q-1) = 2*q-2 by ring,Real.rpow_sub ha,Real.rpow_two]
  field_simp

/-- A uniform weighted difference bound with its constant chosen before the heights. -/
theorem normalPoissonKernel_sub_weight_near {q : ℝ} (hq : q < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2*a →
      IntegrableOn (fun r => |normalPoissonKernel b r-normalPoissonKernel a r| *r^q)
        (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), |normalPoissonKernel b r-normalPoissonKernel a r| *r^q) ≤
        C*(b-a)*a^(2*q-1) := by
  let M : ℝ := ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^q
  let N : ℝ := ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel 1 r*r^(q-1)
  have hC : 0 < 1+|M|+2*|N| := by positivity
  have hMC : M+2*N ≤ 1+|M|+2*|N| := by
    linarith [le_abs_self M,le_abs_self N]
  refine ⟨1+|M|+2*|N|,hC,?_⟩
  intro a b ha hab hba
  refine ⟨normalPoissonKernel_sub_weight_integrable hq ha (ha.trans_le hab),?_⟩
  calc
    _ ≤ (b-a)*a^(2*q-1)*(M+2*N) :=
      normalPoissonKernel_sub_weight_integral_le_near hq ha hab hba
    _ ≤ (b-a)*a^(2*q-1)*(1+|M|+2*|N|) :=
      mul_le_mul_of_nonneg_left hMC
        (mul_nonneg (sub_nonneg.mpr hab) (Real.rpow_nonneg ha.le _))
    _ = _ := by ring

/-- Nearby positive heights satisfy the fractional weighted Poisson difference estimate. -/
theorem normalPoissonKernel_sub_weighted_near {α : ℝ} (_hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 2*a →
      IntegrableOn (fun r => |normalPoissonKernel b r-normalPoissonKernel a r| *r^(α/2))
        (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), |normalPoissonKernel b r-normalPoissonKernel a r| *r^(α/2)) ≤
        C*(b-a)*a^(α-1) := by
  have h := normalPoissonKernel_sub_weight_near (by linarith : α/2 < 1/2)
  simpa only [show 2*(α/2)-1 = α-1 by ring] using h

end Yau.LeafProofs.L16Aux
