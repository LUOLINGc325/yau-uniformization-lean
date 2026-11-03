import Yau.LeafProofs.L19HeatSlabGrowth

/-! Actual compact-region bounds for the boundary commutator in heat duality. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

/-- Local constancy kills the actual differentiated cutoff. -/
theorem scalarGradientPair_zero_of_eventually_const (h : HermitianField M)
    (η k : M.Carrier → ℝ) {x : M.Carrier} {c : ℝ}
    (heq : η =ᶠ[𝓝 x] fun _ => c) : scalarGradientPair h η k x = 0 := by
  have hh := (inChart_eventuallyEq heq).fderiv_eq (𝕜 := ℝ)
  have hd : fderiv ℝ (inChart x η) (chartPt x x) = 0 :=
    hh.trans (fderiv_const_apply c)
  unfold scalarGradientPair chartGradientPair rDeriv
  rw [hd]
  change (((realMetricFn h x (chartPt x x))⁻¹).toBilin' (0 : RIdx n → ℝ))
    (fun b => fderiv ℝ (inChart x k) (chartPt x x) (realVec b)) = 0
  simp only [map_zero, LinearMap.zero_apply]

/-- The gradient of a true radial cutoff is supported in its closed annulus. -/
theorem scalarGradientPair_radial_cutoff_zero_off_annulus
    (g : SmoothMetric M) (o : M.Carrier) {r R : ℝ} (hR : 0 < R)
    {η : M.Carrier → ℝ}
    (hone : ∀ x, inducedDistance g.form o x ≤ r → η x = 1)
    (hsupp : tsupport η ⊆ distBall g.form o R)
    (k : M.Carrier → ℝ) {x : M.Carrier}
    (hx : x ∉ {y | r ≤ inducedDistance g.form o y ∧ inducedDistance g.form o y ≤ R}) :
    scalarGradientPair g.form η k x = 0 := by
  by_cases hxr : inducedDistance g.form o x < r
  · apply scalarGradientPair_zero_of_eventually_const g.form η k (c := 1)
    filter_upwards [(continuous_distFrom g o).continuousAt.eventually (Iio_mem_nhds hxr)] with y hy
    exact hone y hy.le
  · apply scalarGradientPair_zero_of_notMem_tsupport g.form η k
    intro hxη
    have hxR := (L12Aux.mem_distBall_iff g o x hR).mp (hsupp hxη)
    exact hx ⟨le_of_not_gt hxr, hxR.le⟩

/-- The two actual spatial fluxes are bounded by the four local scalar
and gradient energies.  No global integrability premise is used. -/
theorem scalarHeat_commutator_integral_bound
    (g : SmoothMetric M) (hK : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {f k η : M.Carrier → ℝ}
    (hf : SmoothFn f) (hk : SmoothFn k) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    {K : Set M.Carrier} (hcompact : IsCompact K)
    (hzero : ∀ x, x ∉ K → scalarGradientPair g.form η f x = 0 ∧
      scalarGradientPair g.form η k x = 0)
    {B δ : ℝ} (_hB : 0 ≤ B) (hδ : 0 < δ)
    (hbound : ∀ x, scalarGradientPair g.form η η x ≤ B) :
    |∫ x, f x * scalarGradientPair g.form η k x -
      k x * scalarGradientPair g.form η f x ∂μ| ≤
      δ * (∫ x in K, f x ^ 2 ∂μ) + δ⁻¹ * (∫ x in K, k x ^ 2 ∂μ) +
      (δ * B / 4) * (∫ x in K, scalarGradientPair g.form f f x ∂μ) +
      (B / (4 * δ)) * (∫ x in K, scalarGradientPair g.form k k x ∂μ) := by
  have hf2 := smoothFn_integrableOn_compact g μ hμ (smoothFn_pow hf 2) hcompact
  have hk2 := smoothFn_integrableOn_compact g μ hμ (smoothFn_pow hk 2) hcompact
  have hff := smoothFn_integrableOn_compact g μ hμ (smoothFn_scalarGradientPair g hf hf) hcompact
  have hkk := smoothFn_integrableOn_compact g μ hμ (smoothFn_scalarGradientPair g hk hk) hcompact
  have hcomm := (LocalTime.scalar_green_cutoff_commutator g hK μ hμ hf hk hη hcη).2.1
  have hloc : (∫ x, f x * scalarGradientPair g.form η k x -
      k x * scalarGradientPair g.form η f x ∂μ) =
      ∫ x in K, f x * scalarGradientPair g.form η k x -
        k x * scalarGradientPair g.form η f x ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [(hzero x hx).1, (hzero x hx).2]
    ring
  rw [hloc]
  have hp (x : M.Carrier) :
      |f x * scalarGradientPair g.form η k x - k x * scalarGradientPair g.form η f x| ≤
        δ * f x ^ 2 + δ⁻¹ * k x ^ 2 +
          (δ * B / 4) * scalarGradientPair g.form f f x +
          (B / (4 * δ)) * scalarGradientPair g.form k k x := by
    have hh := scalarGradientPair_commutator_young g.form η f k x hδ
    have ha : scalarGradientPair g.form η η x *
        ((δ / 4) * scalarGradientPair g.form f f x) ≤
        B * ((δ / 4) * scalarGradientPair g.form f f x) :=
      mul_le_mul_of_nonneg_right (hbound x)
        (mul_nonneg (by positivity) (scalarGradientPair_self_nonneg g.form f x))
    have hb : scalarGradientPair g.form η η x *
        ((1 / (4 * δ)) * scalarGradientPair g.form k k x) ≤
        B * ((1 / (4 * δ)) * scalarGradientPair g.form k k x) :=
      mul_le_mul_of_nonneg_right (hbound x)
        (mul_nonneg (by positivity) (scalarGradientPair_self_nonneg g.form k x))
    simp only [div_eq_mul_inv, mul_inv_rev] at hh ha hb ⊢
    nlinarith only [hh, ha, hb]
  calc
    _ ≤ ∫ x in K, |f x * scalarGradientPair g.form η k x -
        k x * scalarGradientPair g.form η f x| ∂μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun x => f x * scalarGradientPair g.form η k x -
          k x * scalarGradientPair g.form η f x) (μ := μ.restrict K)
    _ ≤ ∫ x in K, δ * f x ^ 2 + δ⁻¹ * k x ^ 2 +
        (δ * B / 4) * scalarGradientPair g.form f f x +
        (B / (4 * δ)) * scalarGradientPair g.form k k x ∂μ := by
      apply setIntegral_mono_on hcomm.abs.integrableOn
        ((((hf2.const_mul δ).add (hk2.const_mul δ⁻¹)).add
          (hff.const_mul (δ * B / 4))).add (hkk.const_mul (B / (4 * δ)))) hcompact.measurableSet
      intro x _
      exact hp x
    _ = _ := by
      have h₁ := integral_add (((hf2.const_mul δ).add (hk2.const_mul δ⁻¹)).add
        (hff.const_mul (δ * B / 4))) (hkk.const_mul (B / (4 * δ)))
      have h₂ := integral_add ((hf2.const_mul δ).add (hk2.const_mul δ⁻¹))
        (hff.const_mul (δ * B / 4))
      have h₃ := integral_add (hf2.const_mul δ) (hk2.const_mul δ⁻¹)
      simp only [Pi.add_apply] at h₁ h₂ h₃
      rw [h₁, h₂, h₃]
      simp only [integral_const_mul]


end Yau.LeafProofs.L19Aux
