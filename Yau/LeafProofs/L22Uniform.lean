import Yau.LeafProofs.L22LeviBasic

noncomputable section

open scoped Topology ContDiff Matrix ComplexOrder
open Set Filter

namespace Yau.LeafProofs.L22Aux

theorem complexLeviQuadratic_continuousAt {n : ℕ}
    {f : ComplexVector n → ℝ} {p : ComplexVector n}
    (hf : ContDiffAt ℝ ∞ f p) (v : ComplexVector n) :
    ContinuousAt (fun z : ComplexVector n × ComplexVector n =>
      complexLeviQuadratic f z.1 z.2) (p, v) := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) p := hf.fderiv_right (by simp)
  have hdd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ f)) p := hd.fderiv_right (by simp)
  have hH := hdd.continuousAt.comp (continuous_fst.continuousAt (x := (p, v)))
  have hv : ContinuousAt (fun z : ComplexVector n × ComplexVector n => z.2) (p, v) :=
    continuous_snd.continuousAt
  have hIv : ContinuousAt (fun z : ComplexVector n × ComplexVector n => Complex.I • z.2)
      (p, v) := by
    have hI : ContinuousAt (fun _ : ComplexVector n × ComplexVector n => Complex.I) (p, v) :=
      continuousAt_const
    exact hI.smul hv
  exact ((hH.clm_apply hv |>.clm_apply hv).add (hH.clm_apply hIv |>.clm_apply hIv)).div_const 4

/-- Positivity of a continuous quadratic family at one base point gives a
uniform positive lower bound on a neighborhood. Compactness is used only on
the actual unit sphere; no openness claim about arbitrary complex matrices
is involved. -/
theorem exists_uniform_quadratic_positive_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (q : E → E → ℝ) (p : E)
    (hq : ∀ v, ContinuousAt (fun z : E × E => q z.1 z.2) (p, v))
    (hpos : ∀ v, v ≠ 0 → 0 < q p v)
    (hhom : ∀ z v (c : ℝ), q z (c • v) = c ^ 2 * q z v) :
    ∃ r lam : ℝ, 0 < r ∧ 0 < lam ∧
      ∀ z ∈ Metric.ball p r, ∀ v, lam * ‖v‖ ^ 2 ≤ q z v := by
  have hqc : Continuous (q p) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact (hq v).comp (continuous_const.prodMk continuous_id).continuousAt
  have hS : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere _ _
  obtain ⟨m, hm, hmlower⟩ := hS.exists_forall_le' hqc.continuousOn
    (fun v hv => hpos v (by
      intro hv0
      simpa [Metric.mem_sphere, hv0] using hv))
  have hnear : ∀ᶠ z in 𝓝 p, ∀ v ∈ Metric.sphere (0 : E) 1, m / 2 < q z v := by
    apply hS.eventually_forall_of_forall_eventually
    intro v hv
    exact continuousAt_const.eventually_lt (hq v)
      ((half_lt_self hm).trans_le (hmlower v hv))
  obtain ⟨r, hr, hrbound⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, m / 2, hr, half_pos hm, ?_⟩
  intro z hz v
  by_cases hv : v = 0
  · have hqzero : q z 0 = 0 := by simpa using hhom z (0 : E) 0
    simp only [hv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, hqzero, le_refl]
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      dsimp only [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
        inv_mul_cancel₀ hnorm.ne']
    have hqw := (hrbound hz) w hw
    have hvw : ‖v‖ • w = v := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hscale := hhom z w ‖v‖
    rw [hvw] at hscale
    rw [hscale]
    nlinarith [sq_nonneg ‖v‖]

theorem exists_uniform_levi_lower_bound {n : ℕ}
    {f : ComplexVector n → ℝ} {p : ComplexVector n}
    (hf : ContDiffAt ℝ ∞ f p) (hpos : (leviC f p).PosDef) :
    ∃ r lam : ℝ, 0 < r ∧ 0 < lam ∧ ∀ z ∈ Metric.ball p r, ∀ v,
      lam * ‖v‖ ^ 2 ≤ complexLeviQuadratic f z v := by
  apply exists_uniform_quadratic_positive_neighborhood (complexLeviQuadratic f) p
    (complexLeviQuadratic_continuousAt hf)
    ((leviC_posDef_iff (hf.of_le (by simp))).mp hpos)
  intro z v c
  simp only [complexLeviQuadratic, smul_comm Complex.I c, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem exists_uniform_quadratic_bound_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (q : E → E → ℝ) {K : Set E} (hK : IsCompact K)
    (hq : ContinuousOn (fun z : E × E => q z.1 z.2) (K ×ˢ Metric.sphere (0 : E) 1))
    (hhom : ∀ z v (c : ℝ), q z (c • v) = c ^ 2 * q z v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ v, |q z v| ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_bound_of_continuousOn hq
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz v
  by_cases hv : v = 0
  · have hqzero : q z 0 = 0 := by simpa using hhom z (0 : E) 0
    simp [hv, hqzero]
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : E := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
      dsimp only [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
        inv_mul_cancel₀ hnorm.ne']
    have hqwC : |q z w| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (z, w) ⟨hz, hw⟩
    have hqw : |q z w| ≤ max C 0 := hqwC.trans (le_max_left _ _)
    have hvw : ‖v‖ • w = v := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
    have hscale := hhom z w ‖v‖
    rw [hvw] at hscale
    rw [hscale, abs_mul, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg ‖v‖]

theorem exists_uniform_levi_bound_on_compact {n : ℕ}
    {O K : Set (ComplexVector n)} {f : ComplexVector n → ℝ}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ v,
      |complexLeviQuadratic f z v| ≤ C * ‖v‖ ^ 2 := by
  apply exists_uniform_quadratic_bound_on_compact (complexLeviQuadratic f) hK
  · intro zv hzv
    exact (complexLeviQuadratic_continuousAt
      (hf.contDiffAt (hO.mem_nhds (hKO hzv.1))) zv.2).continuousWithinAt
  · intro z v c
    simp only [complexLeviQuadratic, smul_comm Complex.I c, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

end Yau.LeafProofs.L22Aux
