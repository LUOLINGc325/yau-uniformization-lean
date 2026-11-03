import Yau.Proofs.D03RadialFormulas

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Yau.Proofs.D03Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1}


theorem correctionParameter_tendsto : Tendsto correctionParameter atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

theorem correction_radius_bounds (n : ℕ) :
    0 < Real.exp (-2 * correctionParameter n) ∧
      Real.exp (-2 * correctionParameter n) < 1 := by
  exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by nlinarith [correctionParameter_pos n])⟩

theorem correction_exponent_pos (n : ℕ) : 0 < 2 / correctionParameter n :=
  div_pos (by norm_num) (correctionParameter_pos n)

theorem sourceAnnulus_isOpen (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ) :
    IsOpen (sourceAnnulus c n) :=
  (isOpen_lt continuous_const (B01Aux.disc_continuous c hc).norm).inter
    (isOpen_lt (B01Aux.disc_continuous c hc).norm continuous_const)

theorem sourceAnnulus_measurableSet (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ) :
    MeasurableSet (sourceAnnulus c n) := (sourceAnnulus_isOpen c hc n).measurableSet

theorem sourceTail_isOpen (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ) :
    IsOpen (sourceTail c n) :=
  isOpen_lt (B01Aux.disc_continuous c hc).norm continuous_const

theorem sourceTail_measurableSet (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (n : ℕ) :
    MeasurableSet (sourceTail c n) := (sourceTail_isOpen c hc n).measurableSet

theorem weight_exp_neg (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) :
    Real.exp (-weight c n x) = ‖c x‖ ^ (-(2 / correctionParameter n)) *
      Real.exp (-‖c x‖ ^ (1 / correctionParameter n)) := by
  have he : Real.exp (-((2 / correctionParameter n) * Real.log ‖c x‖)) =
      ‖c x‖ ^ (-(2 / correctionParameter n)) := by
    rw [Real.rpow_def_of_pos (B01Aux.disc_mem c hc x).1]
    congr 1
    ring
  rw [weight, neg_add, Real.exp_add, he]

theorem weight_power_ge_one (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) : 1 ≤ ‖c x‖ ^ (-(2 / correctionParameter n)) := by
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (B01Aux.disc_mem c hc x).1
    (B01Aux.disc_mem c hc x).2.le
  exact neg_nonpos.mpr (div_nonneg (by norm_num) (correctionParameter_pos n).le)

theorem weight_power_exp_bounds (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) :
    Real.exp (-1) ≤ Real.exp (-‖c x‖ ^ (1 / correctionParameter n)) ∧
      Real.exp (-‖c x‖ ^ (1 / correctionParameter n)) ≤ 1 := by
  constructor
  · apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.rpow_le_one (B01Aux.disc_mem c hc x).1.le
      (B01Aux.disc_mem c hc x).2.le (one_div_pos.mpr (correctionParameter_pos n)).le)
  · apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Real.rpow_nonneg (norm_nonneg _) _)

theorem discLeviScalar_weight_pos (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) : 0 < discLeviScalar c (weight c n) x := by
  rw [discLeviScalar_weight c hc n x]
  exact mul_pos (inv_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos (correctionParameter_pos n))))
    (Real.rpow_pos_of_pos (B01Aux.disc_mem c hc x).1 _)

theorem discDbarScalar_cutoff_norm (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) :
    ‖discDbarScalar c (cutoff c n) x‖ =
      |deriv radialChi (Real.log ‖c x‖ / correctionParameter n)| /
        (2 * correctionParameter n * ‖c x‖) := by
  rw [discDbarScalar_cutoff c hc]
  simp [Complex.norm_real, abs_of_pos (correctionParameter_pos n)]

theorem discDbarScalar_cutoff_bound (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) :
    ‖discDbarScalar c (cutoff c n) x‖ ≤ cutoffDerivativeBound /
      (correctionParameter n * ‖c x‖) := by
  rw [discDbarScalar_cutoff_norm c hc]
  have ht := correctionParameter_pos n
  have hr := (B01Aux.disc_mem c hc x).1
  have hb := radialChi_deriv_abs_le (Real.log ‖c x‖ / correctionParameter n)
  apply (div_le_iff₀ (by positivity : 0 < 2 * correctionParameter n * ‖c x‖)).2
  have he : cutoffDerivativeBound / (correctionParameter n * ‖c x‖) *
      (2 * correctionParameter n * ‖c x‖) = 2 * cutoffDerivativeBound := by
    field_simp
  rw [he]
  linarith [cutoffDerivativeBound_pos]

theorem discDbarScalar_cutoff_support (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) : Function.support (discDbarScalar c (cutoff c n)) ⊆ sourceAnnulus c n := by
  intro x hx
  have ht := correctionParameter_pos n
  have hr := (B01Aux.disc_mem c hc x).1
  have hd : deriv radialChi (Real.log ‖c x‖ / correctionParameter n) ≠ 0 := by
    intro hzero
    apply hx
    rw [discDbarScalar_cutoff c hc, hzero, Complex.ofReal_zero, zero_div]
  have hlo : -2 < Real.log ‖c x‖ / correctionParameter n := by
    by_contra h
    exact hd (radialChi_deriv_eq_zero (Or.inl (le_of_not_gt h)))
  have hhi : Real.log ‖c x‖ / correctionParameter n < -1 := by
    by_contra h
    exact hd (radialChi_deriv_eq_zero (Or.inr (le_of_not_gt h)))
  constructor
  · apply (Real.lt_log_iff_exp_lt hr).1
    exact (lt_div_iff₀ ht).1 hlo
  · apply (Real.log_lt_iff_lt_exp hr).1
    have h := (div_lt_iff₀ ht).1 hhi
    simpa only [neg_one_mul] using h

theorem discDbarScalar_cutoff_eq_zero_off_annulus (c : DiscCoordinate M)
    (hc : IsDiscCoordinate c) (n : ℕ) (x : M.Carrier) (hx : x ∉ sourceAnnulus c n) :
    discDbarScalar c (cutoff c n) x = 0 := by
  by_contra h
  exact hx (discDbarScalar_cutoff_support c hc n h)

theorem discDbarScalar_cutoff_tsupport (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) : tsupport (discDbarScalar c (cutoff c n)) ⊆
      {x | Real.exp (-2 * correctionParameter n) ≤ ‖c x‖ ∧
        ‖c x‖ ≤ Real.exp (-correctionParameter n)} := by
  apply closure_minimal
  · intro x hx
    exact ⟨(discDbarScalar_cutoff_support c hc n hx).1.le,
      (discDbarScalar_cutoff_support c hc n hx).2.le⟩
  · exact (isClosed_le continuous_const (B01Aux.disc_continuous c hc).norm).inter
      (isClosed_le (B01Aux.disc_continuous c hc).norm continuous_const)

/-- The scalar inverse-curvature estimate uses the same fixed constant at every index. -/
theorem cutoff_inverse_curvature_bound (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) :
    ‖discDbarScalar c (cutoff c n) x‖ ^ 2 / discLeviScalar c (weight c n) x ≤
      cutoffWeightConstant * ‖c x‖ ^ (-(1 / correctionParameter n)) := by
  have ht := correctionParameter_pos n
  have hr := (B01Aux.disc_mem c hc x).1
  have hlevi := discLeviScalar_weight_pos c hc n x
  calc
    _ ≤ (cutoffDerivativeBound / (correctionParameter n * ‖c x‖)) ^ 2 /
        discLeviScalar c (weight c n) x := by
      apply div_le_div_of_nonneg_right _ hlevi.le
      exact pow_le_pow_left₀ (norm_nonneg _) (discDbarScalar_cutoff_bound c hc n x) 2
    _ = _ := by
      rw [discLeviScalar_weight c hc, Real.rpow_sub hr, Real.rpow_neg hr.le,
        Real.rpow_ofNat]
      unfold cutoffWeightConstant
      field_simp
      <;> ring

theorem cutoff_inverse_curvature_eq_zero_off_annulus (c : DiscCoordinate M)
    (hc : IsDiscCoordinate c) (n : ℕ) (x : M.Carrier) (hx : x ∉ sourceAnnulus c n) :
    ‖discDbarScalar c (cutoff c n) x‖ ^ 2 / discLeviScalar c (weight c n) x = 0 := by
  rw [discDbarScalar_cutoff_eq_zero_off_annulus c hc n x hx]
  simp

theorem annulus_negative_power_bound (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) (hx : x ∈ sourceAnnulus c n) :
    ‖c x‖ ^ (-(3 / correctionParameter n)) ≤ Real.exp 6 := by
  rw [Real.rpow_def_of_pos (B01Aux.disc_mem c hc x).1]
  apply Real.exp_le_exp.mpr
  have hlog : -2 * correctionParameter n < Real.log ‖c x‖ :=
    (Real.lt_log_iff_exp_lt (B01Aux.disc_mem c hc x).1).2 hx.1
  have h := (lt_div_iff₀ (correctionParameter_pos n)).2 hlog
  have he : Real.log ‖c x‖ * -(3 / correctionParameter n) =
      -3 * (Real.log ‖c x‖ / correctionParameter n) := by ring
  rw [he]
  linarith


/-- Uniform weighted inverse-curvature bound, localized to the actual source annulus. -/
theorem cutoff_inverse_weighted_bound (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (n : ℕ) (x : M.Carrier) :
    ‖discDbarScalar c (cutoff c n) x‖ ^ 2 / discLeviScalar c (weight c n) x *
      Real.exp (-weight c n x) ≤
      (sourceAnnulus c n).indicator (fun _ => cutoffWeightConstant * Real.exp 6) x := by
  by_cases hx : x ∈ sourceAnnulus c n
  · rw [Set.indicator_of_mem hx]
    have hr := (B01Aux.disc_mem c hc x).1
    calc
      _ ≤ (cutoffWeightConstant * ‖c x‖ ^ (-(1 / correctionParameter n))) *
          Real.exp (-weight c n x) :=
        mul_le_mul_of_nonneg_right (cutoff_inverse_curvature_bound c hc n x) (Real.exp_pos _).le
      _ = cutoffWeightConstant * ‖c x‖ ^ (-(3 / correctionParameter n)) *
          Real.exp (-‖c x‖ ^ (1 / correctionParameter n)) := by
        rw [weight_exp_neg c hc]
        have hp : ‖c x‖ ^ (-(1 / correctionParameter n)) *
            ‖c x‖ ^ (-(2 / correctionParameter n)) =
            ‖c x‖ ^ (-(3 / correctionParameter n)) := by
          rw [← Real.rpow_add hr]
          congr 1
          ring
        calc
          _ = cutoffWeightConstant *
              (‖c x‖ ^ (-(1 / correctionParameter n)) * ‖c x‖ ^ (-(2 / correctionParameter n))) *
              Real.exp (-‖c x‖ ^ (1 / correctionParameter n)) := by ring
          _ = _ := by rw [hp]
      _ ≤ cutoffWeightConstant * Real.exp 6 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (annulus_negative_power_bound c hc n x hx)
            cutoffWeightConstant_pos.le
        · exact (weight_power_exp_bounds c hc n x).2
        · exact (Real.exp_pos _).le
        · exact mul_nonneg cutoffWeightConstant_pos.le (Real.exp_pos _).le
      _ = _ := mul_one _
  · rw [Set.indicator_of_notMem hx, cutoff_inverse_curvature_eq_zero_off_annulus c hc n x hx]
    simp

end Yau.Proofs.D03Aux
