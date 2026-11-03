import Yau.LeafProofs.L16WeakL2Representation
import Yau.LeafProofs.L16InteriorCoefficients
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem memLp_spatialDifferenceQuotient {n : ℕ} {f : Point n → ℝ}
    (hf : MemLp f 2 volume) (e : Space n) (h : ℝ) :
    MemLp (spatialDifferenceQuotient f e h) 2 volume := by
  have hT : MemLp (fun p : Point n => f (p+(h • e,0))) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume (h • e,0))
  convert! (hT.sub hf).const_mul h⁻¹ using 1
  ext p
  simp only [spatialDifferenceQuotient,Prod.add_def,add_zero,smul_eq_mul,Pi.sub_apply]

private theorem abs_integral_mul_le_l2 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ p, f p*g p ∂μ| ≤ (eLpNorm f 2 μ).toReal*(eLpNorm g 2 μ).toReal := by
  have hEq : (∫ p, f p*g p ∂μ) = inner ℝ (hf.toLp f) (hg.toLp g) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with p hfp hgp
    simp only [hfp,hgp,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [hEq,← Real.norm_eq_abs]
  simpa only [Lp.norm_toLp] using norm_inner_le_norm (hf.toLp f) (hg.toLp g)

/-- Haar translation gives the exact adjoint identity for normalized quotients. -/
theorem integral_spatialDifferenceQuotient_mul {n : ℕ} {f φ : Point n → ℝ}
    (hf : MemLp f 2 volume) (hφ : MemLp φ 2 volume) (e : Space n) (h : ℝ) :
    (∫ p, spatialDifferenceQuotient f e h p*φ p) =
      -(∫ p, f p*spatialDifferenceQuotient φ e (-h) p) := by
  let V : Point n := (h • e,0)
  have hfT : MemLp (fun p : Point n => f (p+V)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume V)
  have hφT : MemLp (fun p : Point n => φ (p+-V)) 2 volume :=
    hφ.comp_measurePreserving (measurePreserving_add_right volume (-V))
  have hShift : (∫ p, f (p+V)*φ p) = ∫ p, f p*φ (p+-V) := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun p : Point n => f p*φ (p+-V)) V
    simpa only [add_neg_cancel_right] using h
  have hNeg (p : Point n) : (p.1+(-h) • e,p.2) = p+-V := by
    simp [V,Prod.add_def,neg_smul]
  have hEqL (p : Point n) : spatialDifferenceQuotient f e h p*φ p =
      h⁻¹*(f (p+V)*φ p-f p*φ p) := by
    simp only [spatialDifferenceQuotient,smul_eq_mul,V,Prod.add_def,add_zero]
    ring
  have hEqR (p : Point n) : f p*spatialDifferenceQuotient φ e (-h) p =
      (-h)⁻¹*(f p*φ (p+-V)-f p*φ p) := by
    simp only [spatialDifferenceQuotient,smul_eq_mul,hNeg]
    ring
  have hL : Integrable (fun p => f (p+V)*φ p) volume := hfT.integrable_mul hφ
  have hR : Integrable (fun p => f p*φ (p+-V)) volume := hf.integrable_mul hφT
  have hB : Integrable (fun p => f p*φ p) volume := hf.integrable_mul hφ
  simp_rw [hEqL,hEqR]
  rw [integral_const_mul,integral_const_mul,
    integral_sub hL hB,integral_sub hR hB]
  rw [hShift,inv_neg]
  ring

/-- The classical quotient of a smooth test tends pointwise to its directional derivative. -/
theorem spatialDifferenceQuotient_tendsto {n : ℕ} {φ : Point n → ℝ}
    (hφ : Differentiable ℝ φ) (e : Space n) {h : ℕ → ℝ}
    (hh : ∀ k, h k ≠ 0) (hlim : Tendsto h atTop (𝓝 0)) (p : Point n) :
    Tendsto (fun k => spatialDifferenceQuotient φ e (h k) p) atTop
      (𝓝 (fderiv ℝ φ p (e,0))) := by
  have hLine : HasDerivAt (fun t : ℝ => p+t • (e,0)) (e,0) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const ((e,0) : Point n)).const_add p using 1
    simp only [one_smul]
  have hD : HasDerivAt (fun t : ℝ => φ (p+t • (e,0))) (fderiv ℝ φ p (e,0)) 0 := by
    simpa only [zero_smul,add_zero,Function.comp_def] using
      (hφ (p+0 • (e,0))).hasFDerivAt.comp_hasDerivAt 0 hLine
  have hlim' : Tendsto h atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall hh⟩
  have h := hD.tendsto_slope_zero.comp hlim'
  simpa only [spatialDifferenceQuotient,Prod.smul_mk,smul_zero,Prod.add_def,add_zero,
    zero_add,zero_smul,Function.comp_def] using h

/-- Pairing a global `L²` function with a smooth compact quotient converges to
the pairing with the classical directional derivative. -/
theorem integral_mul_spatialDifferenceQuotient_tendsto {n : ℕ} {f φ : Point n → ℝ}
    (hf : MemLp f 2 volume) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (e : Space n) {h : ℕ → ℝ} (hh : ∀ k, h k ≠ 0)
    (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun k => ∫ p, f p*spatialDifferenceQuotient φ e (h k) p) atTop
      (𝓝 (∫ p, f p*fderiv ℝ φ p (e,0))) := by
  obtain ⟨L,hL,_hValue,_hDeriv,hLip⟩ := smooth_compact_global_bounds hφ hcφ
  obtain ⟨R,_hRpos,hR⟩ := hcφ.isBounded.exists_pos_norm_le
  obtain ⟨H,_hHpos,hH⟩ := hlim.cauchySeq.isBounded_range.exists_pos_norm_le
  let K : Set (Point n) := Metric.closedBall 0 (R+H*‖e‖)
  have hK : IsCompact K := isCompact_closedBall _ _
  let B : ℝ := L*‖e‖
  let bound : Point n → ℝ := K.indicator (fun p => ‖f p‖*B)
  have hb : Integrable bound volume := by
    apply IntegrableOn.integrable_indicator (s := K) _ hK.measurableSet
    exact ((hf.locallyIntegrable (by norm_num)).integrableOn_isCompact hK).norm.mul_const B
  apply tendsto_integral_of_dominated_convergence bound
  · intro k
    exact hf.aestronglyMeasurable.mul
      (contDiff_spatialDifferenceQuotient hφ e (h k)).continuous.aestronglyMeasurable
  · exact hb
  · intro k
    apply Eventually.of_forall
    intro p
    by_cases hp : p ∈ K
    · simp only [bound,Set.indicator_of_mem hp,norm_mul]
      exact mul_le_mul_of_nonneg_left
        (spatialDifferenceQuotient_norm_le_of_lipschitz hL.le hLip e (h k) p)
        (norm_nonneg _)
    · have hpNorm : R+H*‖e‖ < ‖p‖ := by
        simpa only [K,Metric.mem_closedBall,dist_zero_right,not_le] using hp
      have hφp : φ p = 0 := by
        by_contra hz
        have hpr := hR p (subset_tsupport φ (Function.mem_support.mpr hz))
        have hH0 : 0 ≤ H*‖e‖ := mul_nonneg _hHpos.le (norm_nonneg _)
        linarith
      let V : Point n := ((h k) • e,0)
      have hV : ‖V‖ ≤ H*‖e‖ := by
        have hVk : ‖V‖ = |h k| * ‖e‖ := by
          simp only [V,Prod.norm_def,norm_smul,Real.norm_eq_abs,norm_zero,
            max_eq_left (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
        rw [hVk]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [Real.norm_eq_abs] using hH (h k) (Set.mem_range_self k))
          (norm_nonneg _)
      have hTri : ‖p‖ ≤ ‖p+V‖+‖V‖ := by
        calc
          ‖p‖ = ‖(p+V)-V‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖p+V‖+‖V‖ := norm_sub_le _ _
      have hφT : φ (p+V) = 0 := by
        by_contra hz
        have hpr := hR (p+V) (subset_tsupport φ (Function.mem_support.mpr hz))
        linarith
      have hDQ : spatialDifferenceQuotient φ e (h k) p = 0 := by
        change (h k)⁻¹ • (φ (p.1+h k • e,p.2)-φ p) = 0
        have hφT' : φ (p.1+h k • e,p.2) = 0 := by
          simpa only [V,Prod.add_def,add_zero] using hφT
        simp only [hφT',hφp,sub_self,smul_zero]
      simp only [bound,Set.indicator_of_notMem hp,hDQ,mul_zero,norm_zero,le_refl]
  · apply Eventually.of_forall
    intro p
    exact (spatialDifferenceQuotient_tendsto (hφ.differentiable (by simp)) e hh hlim p).const_mul (f p)

private theorem integral_mul_test_restrict {n : ℕ} {U : Set (Point n)}
    {φ : Point n → ℝ} (hφ : Test U φ) (f : Point n → ℝ) :
    (∫ p, f p*φ p ∂volume.restrict U) = ∫ p, f p*φ p := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hp' : p ∉ tsupport φ := fun h => hp (hφ.2.2 h)
  simp only [image_eq_zero_of_notMem_tsupport hp',mul_zero]

/-- A uniform local `L²` bound on genuine difference quotients produces an
actual local weak derivative, with the very same bound. -/
theorem exists_memLp_weak_directionalDerivative_of_spatialDifferenceQuotient_bound
    {n : ℕ} {U : Set (Point n)} (hU : IsOpen U) (e : Space n)
    {f : Point n → ℝ} (hf : MemLp f 2 volume) (C : ℝ) (hC : 0 ≤ C)
    {h : ℕ → ℝ} (hh : ∀ k, h k ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hBound : ∀ k, eLpNorm (spatialDifferenceQuotient f e (h k)) 2
      (volume.restrict U) ≤ ENNReal.ofReal C) :
    ∃ g : Point n → ℝ, MemLp g 2 (volume.restrict U) ∧
      eLpNorm g 2 (volume.restrict U) ≤ ENNReal.ofReal C ∧
      ∀ φ : Point n → ℝ, Test U φ →
        (∫ p, f p*fderiv ℝ φ p (e,0) ∂volume.restrict U) =
          -(∫ p, g p*φ p ∂volume.restrict U) := by
  apply exists_memLp_weak_directionalDerivative_of_bound hU (e,0) f (hf.restrict U) C hC
  intro φ hφ
  have hφLp : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
  have hLim := integral_mul_spatialDifferenceQuotient_tendsto hf hφ.1 hφ.2.1 e
    (fun k => neg_ne_zero.mpr (hh k)) (by simpa only [neg_zero] using hlim.neg)
  have hB (k : ℕ) : |∫ p, f p*spatialDifferenceQuotient φ e (-(h k)) p| ≤
      C*(eLpNorm φ 2 (volume.restrict U)).toReal := by
    have hPair := abs_integral_mul_le_l2
      ((memLp_spatialDifferenceQuotient hf e (h k)).restrict U) (test_memLp hφ)
    have hNorm : (eLpNorm (spatialDifferenceQuotient f e (h k)) 2
        (volume.restrict U)).toReal ≤ C := by
      have hN := ENNReal.toReal_mono (by simp) (hBound k)
      simpa only [ENNReal.toReal_ofReal hC] using hN
    have hRes := integral_mul_test_restrict hφ (spatialDifferenceQuotient f e (h k))
    rw [hRes,integral_spatialDifferenceQuotient_mul hf hφLp e (h k),abs_neg] at hPair
    exact hPair.trans (mul_le_mul_of_nonneg_right hNorm ENNReal.toReal_nonneg)
  have hFinal := le_of_tendsto hLim.abs (Eventually.of_forall hB)
  rw [integral_mul_test_restrict (test_directionalDerivative hφ (e,0)) f]
  exact hFinal

/-- The local quotient criterion with a nonnegative real bound. -/
theorem exists_memLp_weak_directionalDerivative_of_spatialDifferenceQuotient_norm_bound
    {n : ℕ} {U : Set (Point n)} (hU : IsOpen U) (e : Space n)
    {f : Point n → ℝ} (hf : MemLp f 2 volume) (C : ℝ≥0)
    {h : ℕ → ℝ} (hh : ∀ k, h k ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hBound : ∀ k, eLpNorm (spatialDifferenceQuotient f e (h k)) 2
      (volume.restrict U) ≤ ENNReal.ofReal (C : ℝ)) :
    ∃ g : Point n → ℝ, MemLp g 2 (volume.restrict U) ∧
      eLpNorm g 2 (volume.restrict U) ≤ ENNReal.ofReal (C : ℝ) ∧
      ∀ φ : Point n → ℝ, Test U φ →
        (∫ p, f p*fderiv ℝ φ p (e,0) ∂volume.restrict U) =
          -(∫ p, g p*φ p ∂volume.restrict U) :=
  exists_memLp_weak_directionalDerivative_of_spatialDifferenceQuotient_bound
    hU e hf C C.coe_nonneg hh hlim hBound

/-- The same local criterion in the squared-integral form supplied by energy
estimates. Membership of each quotient in `L²` follows from global `f ∈ L²`. -/
theorem exists_memLp_weak_directionalDerivative_of_spatialDifferenceQuotient_sq_bound
    {n : ℕ} {U : Set (Point n)} (hU : IsOpen U) (e : Space n)
    {f : Point n → ℝ} (hf : MemLp f 2 volume) (C : ℝ) (hC : 0 ≤ C)
    {h : ℕ → ℝ} (hh : ∀ k, h k ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hBound : ∀ k, (∫ p, (spatialDifferenceQuotient f e (h k) p)^2
      ∂volume.restrict U) ≤ C^2) :
    ∃ g : Point n → ℝ, MemLp g 2 (volume.restrict U) ∧
      eLpNorm g 2 (volume.restrict U) ≤ ENNReal.ofReal C ∧
      ∀ φ : Point n → ℝ, Test U φ →
        (∫ p, f p*fderiv ℝ φ p (e,0) ∂volume.restrict U) =
          -(∫ p, g p*φ p ∂volume.restrict U) := by
  apply exists_memLp_weak_directionalDerivative_of_spatialDifferenceQuotient_bound
    hU e hf C hC hh hlim
  intro k
  let q : Point n → ℝ := spatialDifferenceQuotient f e (h k)
  have hq : MemLp q 2 (volume.restrict U) :=
    (memLp_spatialDifferenceQuotient hf e (h k)).restrict U
  have hInner : inner ℝ (hq.toLp q) (hq.toLp q) =
      ∫ p, (q p)^2 ∂volume.restrict U := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hq.coeFn_toLp] with p hp
    simp only [hp,RCLike.inner_apply,conj_trivial,pow_two]
  have hSq : ((eLpNorm q 2 (volume.restrict U)).toReal)^2 =
      ∫ p, (q p)^2 ∂volume.restrict U := by
    calc
      _ = ‖hq.toLp q‖^2 := by simp only [Lp.norm_toLp]
      _ = inner ℝ (hq.toLp q) (hq.toLp q) := (real_inner_self_eq_norm_sq _).symm
      _ = _ := hInner
  have hNorm : (eLpNorm q 2 (volume.restrict U)).toReal ≤ C := by
    have h := hBound k
    change (∫ p, (q p)^2 ∂volume.restrict U) ≤ C^2 at h
    rw [← hSq] at h
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm q 2 (volume.restrict U))]
  change eLpNorm q 2 (volume.restrict U) ≤ ENNReal.ofReal C
  rw [← ENNReal.ofReal_toReal hq.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hNorm

/-- The global specialization of the local quotient criterion. -/
theorem exists_memLp_global_weak_directionalDerivative_of_spatialDifferenceQuotient_bound
    {n : ℕ} (e : Space n) {f : Point n → ℝ} (hf : MemLp f 2 volume)
    (C : ℝ) (hC : 0 ≤ C) {h : ℕ → ℝ} (hh : ∀ k, h k ≠ 0)
    (hlim : Tendsto h atTop (𝓝 0))
    (hBound : ∀ k, eLpNorm (spatialDifferenceQuotient f e (h k)) 2 volume ≤
      ENNReal.ofReal C) :
    ∃ g : Point n → ℝ, MemLp g 2 volume ∧ eLpNorm g 2 volume ≤ ENNReal.ofReal C ∧
      ∀ φ : Point n → ℝ, Test Set.univ φ →
        (∫ p, f p*fderiv ℝ φ p (e,0)) = -(∫ p, g p*φ p) := by
  simpa only [Measure.restrict_univ] using
    exists_memLp_weak_directionalDerivative_of_spatialDifferenceQuotient_bound
      isOpen_univ e hf C hC hh hlim (by simpa only [Measure.restrict_univ] using hBound)

end Yau.LeafProofs.L16Aux
