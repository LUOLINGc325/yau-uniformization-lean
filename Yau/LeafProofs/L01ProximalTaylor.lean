import Yau.LeafProofs.L01Envelope
import Yau.LeafProofs.L01EnvelopeTaylor
import Yau.LeafProofs.L01RegularInverse

open Set Filter Asymptotics
open scoped Topology InnerProductSpace

namespace Yau.LeafProofs.L01Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Completing the square in an invertible symmetric bilinear form. -/
theorem inverse_quadratic_identity (T : E ≃L[ℝ] E)
    (hsym : ∀ v w, ⟪T v, w⟫_ℝ = ⟪T w, v⟫_ℝ) (v h : E) :
    ⟪v, h⟫_ℝ - (1 / 2) * ⟪T h, h⟫_ℝ - (1 / 2) * ⟪T.symm v, v⟫_ℝ =
      -(1 / 2) * ⟪T.symm (v - T h), v - T h⟫_ℝ := by
  have hi : ⟪T.symm v, T h⟫_ℝ = ⟪v, h⟫_ℝ := by
    rw [real_inner_comm]
    simpa only [T.apply_symm_apply] using (hsym (T.symm v) h).symm
  rw [map_sub, T.symm_apply_apply]
  simp only [inner_sub_left, inner_sub_right]
  rw [hi, real_inner_comm h v, real_inner_comm h (T h)]
  ring

/-- The exact envelope identity for the primal second-order remainder. -/
theorem proximal_residual_identity (f : E → ℝ) (P : E → E)
    (y₀ q : E) (T : E ≃L[ℝ] E)
    (hsym : ∀ v w, ⟪T v, w⟫_ℝ = ⟪T w, v⟫_ℝ) :
    f (P q) - f (P y₀) - ⟪y₀ - P y₀, P q - P y₀⟫_ℝ -
      (1 / 2) * ⟪T.symm (P q - P y₀) - (P q - P y₀), P q - P y₀⟫_ℝ =
    -(envelope f P q - envelope f P y₀ - ⟪P y₀, q - y₀⟫_ℝ -
      (1 / 2) * ⟪T (q - y₀), q - y₀⟫_ℝ) -
      (1 / 2) * ⟪T.symm (P q - P y₀ - T (q - y₀)), P q - P y₀ - T (q - y₀)⟫_ℝ := by
  have hquad := inverse_quadratic_identity T hsym (P q - P y₀) (q - y₀)
  have hnorm := norm_sub_sq_real (P q) (P y₀)
  rw [primal_eq_of_envelope f P q, primal_eq_of_envelope f P y₀]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at hquad ⊢
  nlinarith only [hquad, hnorm, real_inner_comm (P y₀) (P q),
    real_inner_comm (P q) q, real_inner_comm (P q) y₀, real_inner_comm (P y₀) q,
    real_inner_comm (P y₀) y₀]

/-- The deterministic transfer of the envelope jet to an interior primal point. -/
theorem second_peano_of_proximal_regular_equiv [FiniteDimensional ℝ E]
    (K : Set E) (f : E → ℝ) (P : E → E)
    (hK : IsCompact K) (hcont : ContinuousOn f K)
    (hmem : ∀ y, P y ∈ K)
    (hmin : ∀ y z, z ∈ K → proxCost f y (P y) ≤ proxCost f y z)
    (hfirm : ∀ y w, ‖P y - P w‖ ^ 2 ≤ ⟪P y - P w, y - w⟫_ℝ)
    (hLip : LipschitzWith 1 P)
    (y₀ : E) (hy₀ : P y₀ ∈ interior K)
    (T : E ≃L[ℝ] E) (hT : HasFDerivAt P T.toContinuousLinearMap y₀) :
    ∃ (p : E →L[ℝ] ℝ) (A : E →L[ℝ] E →L[ℝ] ℝ),
      (∀ v w, A v w = A w v) ∧
      (fun z => f z - f (P y₀) - p (z - P y₀) -
        (1 / 2) * A (z - P y₀) (z - P y₀))
        =o[𝓝 (P y₀)] (fun z => ‖z - P y₀‖ ^ 2) := by
  let S : E →L[ℝ] E := T.symm
  obtain ⟨hsym, hR⟩ := second_peano_of_gradient_hasFDerivAt (envelope f P) P
    (envelope_hasFDerivAt hmem hmin hLip) y₀ T.toContinuousLinearMap hT
  have hSsym (v w : E) : ⟪S v, w⟫_ℝ = ⟪S w, v⟫_ℝ := by
    have h := hsym (T.symm v) (T.symm w)
    change ⟪T (T.symm v), T.symm w⟫_ℝ = ⟪T (T.symm w), T.symm v⟫_ℝ at h
    rw [T.apply_symm_apply, T.apply_symm_apply,
      real_inner_comm (T.symm w) v, real_inner_comm (T.symm v) w] at h
    exact h.symm
  let p := innerSL ℝ (y₀ - P y₀)
  let A := (innerSL ℝ).comp (S - ContinuousLinearMap.id ℝ E)
  refine ⟨p, A, ?_, ?_⟩
  · intro v w
    change ⟪S v - v, w⟫_ℝ = ⟪S w - w, v⟫_ℝ
    rw [inner_sub_left, inner_sub_left, hSsym, real_inner_comm v w]
  obtain ⟨C, δ, hC, hδ, hpre⟩ :=
    preimage_norm_le_of_firm_of_hasFDerivAt_equiv P hfirm y₀ T hT
  have hrange := interior_subset_range_prox K f P hK hcont hmem hmin hLip
  let R : E → ℝ := fun q => envelope f P q - envelope f P y₀ - ⟪P y₀, q - y₀⟫_ℝ -
    (1 / 2) * ⟪T (q - y₀), q - y₀⟫_ℝ
  let e : E → E := fun q => P q - P y₀ - T (q - y₀)
  have he : e =o[𝓝 y₀] (fun q => q - y₀) := hasFDerivAt_iff_isLittleO.mp hT
  apply isLittleO_iff.2
  intro ε hε
  let η := ε / ((1 + ‖S‖) * C ^ 2)
  have hη : 0 < η := div_pos hε (mul_pos (by positivity) (sq_pos_of_pos hC))
  have hηeq : (1 + ‖S‖) * η * C ^ 2 = ε := by
    dsimp [η]
    field_simp
  have hdual : ∀ᶠ q in 𝓝 y₀,
      ‖R q‖ ≤ η * ‖q - y₀‖ ^ 2 ∧
      ‖e q‖ ≤ ‖q - y₀‖ ∧ ‖e q‖ ≤ η * ‖q - y₀‖ := by
    filter_upwards [hR.bound hη, he.bound (show (0 : ℝ) < 1 by norm_num), he.bound hη]
      with q hqR hq₁ hqη
    exact ⟨by simpa only [R, ContinuousLinearEquiv.coe_coe, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖q - y₀‖)] using hqR,
      by simpa only [one_mul] using hq₁, hqη⟩
  obtain ⟨r, hr, hdualb⟩ := Metric.eventually_nhds_iff.mp hdual
  let ζ := min δ (r / C)
  have hζ : 0 < ζ := lt_min hδ (div_pos hr hC)
  filter_upwards [Metric.ball_mem_nhds (P y₀) hζ, isOpen_interior.mem_nhds hy₀]
    with z hz hzin
  obtain ⟨q, hq⟩ := hrange hzin
  have hzdist : ‖z - P y₀‖ < ζ := by simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hnear : ‖P q - P y₀‖ < δ := by rw [hq]; exact hzdist.trans_le (min_le_left _ _)
  have hcontrol := hpre q hnear
  rw [hq] at hcontrol
  have hqr : dist q y₀ < r := by
    rw [dist_eq_norm]
    have hzr : ‖z - P y₀‖ * C < r :=
      (lt_div_iff₀ hC).mp (hzdist.trans_le (min_le_right _ _))
    exact hcontrol.trans_lt (by simpa only [mul_comm] using hzr)
  obtain ⟨hqR, hq₁, hqη⟩ := hdualb hqr
  have hesq : ‖e q‖ ^ 2 ≤ η * ‖q - y₀‖ ^ 2 := by
    have h := mul_le_mul hqη hq₁ (norm_nonneg (e q))
      (mul_nonneg hη.le (norm_nonneg (q - y₀)))
    nlinarith only [h]
  have hinner : ‖⟪S (e q), e q⟫_ℝ‖ ≤ ‖S‖ * η * ‖q - y₀‖ ^ 2 := by
    calc
      ‖⟪S (e q), e q⟫_ℝ‖ ≤ ‖S (e q)‖ * ‖e q‖ := norm_inner_le_norm _ _
      _ ≤ (‖S‖ * ‖e q‖) * ‖e q‖ :=
        mul_le_mul_of_nonneg_right (S.le_opNorm _) (norm_nonneg _)
      _ = ‖S‖ * ‖e q‖ ^ 2 := by ring
      _ ≤ ‖S‖ * (η * ‖q - y₀‖ ^ 2) := mul_le_mul_of_nonneg_left hesq (norm_nonneg S)
      _ = ‖S‖ * η * ‖q - y₀‖ ^ 2 := by ring
  have hidentity := proximal_residual_identity f P y₀ q T hsym
  change f (P q) - f (P y₀) - p (P q - P y₀) -
    (1 / 2) * A (P q - P y₀) (P q - P y₀) =
    -R q - (1 / 2) * ⟪S (e q), e q⟫_ℝ at hidentity
  rw [hq] at hidentity
  rw [hidentity]
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖z - P y₀‖)]
  have hn : ‖q - y₀‖ ^ 2 ≤ C ^ 2 * ‖z - P y₀‖ ^ 2 := by
    have h := mul_le_mul hcontrol hcontrol (norm_nonneg _) (mul_nonneg hC.le (norm_nonneg _))
    nlinarith only [h]
  have herr : |-R q - (1 / 2) * ⟪S (e q), e q⟫_ℝ| ≤
      (1 + ‖S‖) * η * ‖q - y₀‖ ^ 2 := by
    have htri := norm_sub_le (-R q) ((1 / 2 : ℝ) * ⟪S (e q), e q⟫_ℝ)
    simp only [norm_neg, norm_mul, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at htri
    rw [Real.norm_eq_abs] at hqR hinner
    have hnonneg := mul_nonneg (norm_nonneg S) (mul_nonneg hη.le (sq_nonneg ‖q - y₀‖))
    nlinarith only [htri, hqR, hinner, hnonneg]
  calc
    |-R q - (1 / 2) * ⟪S (e q), e q⟫_ℝ| ≤ (1 + ‖S‖) * η * ‖q - y₀‖ ^ 2 := herr
    _ ≤ (1 + ‖S‖) * η * (C ^ 2 * ‖z - P y₀‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hn (mul_nonneg (by positivity) hη.le)
    _ = ε * ‖z - P y₀‖ ^ 2 := by rw [← mul_assoc, hηeq]

theorem second_peano_of_proximal_regular [FiniteDimensional ℝ E]
    (K : Set E) (f : E → ℝ) (P : E → E)
    (hK : IsCompact K) (hcont : ContinuousOn f K)
    (hmem : ∀ y, P y ∈ K)
    (hmin : ∀ y z, z ∈ K → proxCost f y (P y) ≤ proxCost f y z)
    (hfirm : ∀ y w, ‖P y - P w‖ ^ 2 ≤ ⟪P y - P w, y - w⟫_ℝ)
    (hLip : LipschitzWith 1 P)
    (y₀ : E) (hy₀ : P y₀ ∈ interior K)
    (T : E →L[ℝ] E) (hT : HasFDerivAt P T y₀) (hdet : T.det ≠ 0) :
    ∃ (p : E →L[ℝ] ℝ) (A : E →L[ℝ] E →L[ℝ] ℝ),
      (∀ v w, A v w = A w v) ∧
      (fun z => f z - f (P y₀) - p (z - P y₀) -
        (1 / 2) * A (z - P y₀) (z - P y₀))
        =o[𝓝 (P y₀)] (fun z => ‖z - P y₀‖ ^ 2) := by
  apply second_peano_of_proximal_regular_equiv K f P hK hcont hmem hmin hfirm hLip
    y₀ hy₀ (T.toContinuousLinearEquivOfDetNeZero hdet)
  simpa only [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using hT

end Yau.LeafProofs.L01Aux
