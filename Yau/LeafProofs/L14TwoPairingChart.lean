import Yau.LeafProofs.L14TwoAdjointModel
import Yau.LeafProofs.L14TwoL2

/-! The actual complex degree-two pairing against a compact chart test, with only local L² on the source. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal Kronecker
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem twoCoefficient_cross_contraction {n r : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (H : Matrix (Fin r) (Fin r) ℂ)
    (U V : Fin r → Fin n → Fin n → ℂ) (d ρ : ℂ) :
    (∑ i, ∑ k, ∑ j, ∑ l, G i k * G j l *
      ((∑ α, ∑ β, star (U α i j) * H α β * V β k l) / d)) * ρ =
      d⁻¹ * ∑ i, ∑ j, ∑ α, star (U α i j) *
        (ρ * (((H ⊗ₖ G) ⊗ₖ G) *ᵥ
          (fun p : (Fin r × Fin n) × Fin n => V p.1.1 p.1.2 p.2)) ((α,i),j)) := by
  classical
  let e : (Fin n × Fin n × Fin n × Fin n × Fin r × Fin r) ≃
      (Fin n × Fin n × Fin r × Fin r × Fin n × Fin n) :=
    { toFun := fun ⟨i,k,j,l,α,β⟩ => (i,j,α,β,k,l)
      invFun := fun ⟨i,j,α,β,k,l⟩ => (i,k,j,l,α,β)
      left_inv := by rintro ⟨i,k,j,l,α,β⟩; rfl
      right_inv := by rintro ⟨i,j,α,β,k,l⟩; rfl }
  have hp (f : Fin n → Fin n → Fin n → Fin n → Fin r → Fin r → ℂ) :
      (∑ i, ∑ k, ∑ j, ∑ l, ∑ α, ∑ β, f i k j l α β) =
      ∑ i, ∑ j, ∑ α, ∑ β, ∑ k, ∑ l, f i k j l α β := by
    simpa only [Fintype.sum_prod_type] using Fintype.sum_equiv e
      (fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (fun p => f p.1 p.2.2.2.2.1 p.2.1 p.2.2.2.2.2 p.2.2.1 p.2.2.2.1)
      (by rintro ⟨i,k,j,l,α,β⟩; rfl)
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  rw [hp]
  repeat' apply Finset.sum_congr rfl; intro _ _
  ring

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem integrable_of_bundleChart_density (g : Yau.SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (a : M.Carrier)
    (P : M.Carrier → ℂ) (Q : ComplexVector n → ℂ)
    (hP : AEMeasurable P μ) (hQ : Integrable Q (lebesgueC n))
    (hPzero : ∀ x, x ∉ bundleChartSource (r := r) E a → P x = 0)
    (hlocal : ∀ z ∈ localDomain (r := r) E a,
      Real.sqrt (realMetricFn g.form a z).det • P (chartInv a z) = (2 : ℝ) ^ n • Q z) :
    Integrable P μ := by
  have hnorm : (∫⁻ x, ENNReal.ofReal ‖P x‖ ∂μ) =
      ENNReal.ofReal ((2 : ℝ) ^ n) * ∫⁻ z in localDomain (r := r) E a,
        ENNReal.ofReal ‖Q z‖ ∂lebesgueC n := by
    calc
      _ = ∫⁻ x in bundleChartSource (r := r) E a, ENNReal.ofReal ‖P x‖ ∂μ := by
        symm
        apply setLIntegral_eq_of_support_subset
        intro x hx
        by_contra hn
        exact hx (by simp [hPzero x hn])
      _ = ∫⁻ z in localDomain (r := r) E a,
          ENNReal.ofReal (Real.sqrt (realMetricFn g.form a z).det) *
            ENNReal.ofReal ‖P (chartInv a z)‖ ∂lebesgueC n :=
        lintegral_bundleChart_volume E g μ hμ a _ (ENNReal.measurable_ofReal.comp_aemeasurable hP.norm)
      _ = _ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (localDomain_isOpen E a).measurableSet] with z hz
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
          ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
        congr 1
        have he := congrArg norm (hlocal z hz)
        simpa only [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          Real.norm_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)] using he
  refine ⟨hP.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, hnorm]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((hasFiniteIntegral_iff_norm Q).mp (hQ.mono_measure Measure.restrict_le_self).2)

theorem weightedTwoPairing_eq_zero_of_right_zero (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u v : NQForm E 2) (x : M.Carrier)
    (hx : v x = (0 : NQForm E 2) x) : weightedTwoPairing E g h φ u v x = 0 := by
  have he : twoFormPairing E g h u v x = twoFormPairing E g h u (0 : NQForm E 2) x := by
    unfold twoFormPairing
    rw [hx]
  have hz : twoFormPairing E g h u (0 : NQForm E 2) x = 0 := by
    simpa only [zero_smul, zero_mul] using
      (twoFormPairing_smul_right E g h (0 : ℂ) u (0 : NQForm E 2) x)
  simp only [weightedTwoPairing, he, hz, zero_mul]

theorem weightedTwoPairing_twoFormPushforward_density (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 2) (a : M.Carrier)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hskew : ∀ z i j, F z j i = -F z i j)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) :
    Real.sqrt (realMetricFn g a z).det •
      weightedTwoPairing E g h φ u (twoFormPushforward E a F) (chartInv a z) =
      (2 : ℝ) ^ n • ((1 / 2 : ℂ) * ∑ i, ∑ j, ∑ α,
        star (coefficients (r := r) E u a z ![i,j] α) * chartTwoDual E g h φ a F z i j α) := by
  rw [weightedTwoPairing, twoFormPairing_inChart E g h u _ a z hz,
    realMetricFn_sqrt_det g a z hz.1]
  simp_rw [twoFormPushforward_coefficients E a F hskew z hz]
  let S := ∑ i, ∑ k, ∑ j, ∑ l, (hMat g a z)⁻¹ i k * (hMat g a z)⁻¹ j l *
    ((∑ α, ∑ β, star (coefficients (r := r) E u a z ![i,j] α) *
      BundleDbar.metricMatrix (r := r) E h a z α β * F z k l β) / ((hMat g a z).det.re : ℂ))
  have he := twoCoefficient_cross_contraction (hMat g a z)⁻¹ (BundleDbar.metricMatrix (r := r) E h a z)
    (fun α i j => coefficients (r := r) E u a z ![i,j] α) (fun α i j => F z i j α)
    ((hMat g a z).det.re : ℂ) (Real.exp (-φ (chartInv a z)) : ℂ)
  have he' : S * (Real.exp (-φ (chartInv a z)) : ℂ) =
      ((hMat g a z).det.re : ℂ)⁻¹ * ∑ i, ∑ j, ∑ α,
        star (coefficients (r := r) E u a z ![i,j] α) * chartTwoDual E g h φ a F z i j α := he
  change (((2 : ℝ) ^ n * (hMat g a z).det.re) : ℝ) •
    (((1 / 2 : ℂ) * S) * (Real.exp (-φ (chartInv a z)) : ℂ)) = _
  rw [show ((1 / 2 : ℂ) * S) * (Real.exp (-φ (chartInv a z)) : ℂ) =
      (1 / 2 : ℂ) * (S * (Real.exp (-φ (chartInv a z)) : ℂ)) by ring, he']
  simp only [Complex.real_smul, Complex.ofReal_mul]
  have hd : ((hMat g a z).det.re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (L18Aux.hMat_det_re_pos g a hz.1))
  field_simp [hd]

theorem chartTwoDual_conjugate_test_integrable (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 2) (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) (i j : Fin n) (α : Fin r) :
    Integrable (fun z => star (coefficients (r := r) E u a z ![i,j] α) *
      chartTwoDual E g.form h φ a F z i j α) (lebesgueC n) := by
  have hsub := tsupport_chartTwoDual_subset E g.form h φ a F i j α
  exact locallyL2_conjugate_test_integrable E u hu a ![i,j] α _
    (chartTwoDual_contDiff E g h hh φ hφ a F hF hs i j α).continuous
    (hc.of_isClosed_subset (isClosed_tsupport _) hsub) (hsub.trans hs)

set_option backward.isDefEq.respectTransparency false in
theorem weightedTwoPairing_twoFormPushforward_integrable (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (hE : Holomorphic (r := r) E) (u : NQForm E 2) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a)
    (hskew : ∀ z i j, F z j i = -F z i j) :
    Integrable (weightedTwoPairing E g.form h φ u (twoFormPushforward E a F)) μ := by
  classical
  let v := twoFormPushforward (r := r) E a F
  let Q := fun z => (1 / 2 : ℂ) * ∑ i, ∑ j, ∑ α,
    star (coefficients (r := r) E u a z ![i,j] α) * chartTwoDual E g.form h φ a F z i j α
  have hQ : Integrable Q (lebesgueC n) := by
    apply Integrable.const_mul
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun α _ => chartTwoDual_conjugate_test_integrable
        E g h hh φ hφ u hu a F hF hc hs i j α)))
  have hv : LocallyL2 (r := r) E v := smoothForm_locallyL2 E v
    (twoFormPushforward_smooth E hE a F hskew hF hc hs)
  have hw : AEMeasurable (fun x => (Real.exp (-φ x) : ℂ)) μ :=
    Complex.continuous_ofReal.measurable.comp_aemeasurable
      (Real.continuous_exp.comp (L18Aux.continuous_of_smoothFn hφ).neg).measurable.aemeasurable
  have hm : AEMeasurable (weightedTwoPairing E g.form h φ u v) μ :=
    (twoFormPairing_aemeasurable E g μ hμ h hh u v hu hv).mul hw
  apply integrable_of_bundleChart_density (r := r) E g μ hμ a _ Q hm hQ
  · intro x hx
    apply weightedTwoPairing_eq_zero_of_right_zero
    change (if hy : x ∈ bundleChartSource (r := r) E a then _ else _) = _
    exact dite_eq_right hx
  · exact weightedTwoPairing_twoFormPushforward_density E g.form h φ u a F hskew

set_option backward.isDefEq.respectTransparency false in
theorem weightedTwoPairing_twoFormPushforward_integral (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (hE : Holomorphic (r := r) E) (u : NQForm E 2) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a)
    (hskew : ∀ z i j, F z j i = -F z i j) :
    (∫ x, weightedTwoPairing E g.form h φ u (twoFormPushforward E a F) x ∂μ) =
      (2 : ℝ) ^ n • ((1 / 2 : ℂ) * ∑ i, ∑ j, ∑ α,
        ∫ z, star (coefficients (r := r) E u a z ![i,j] α) *
          chartTwoDual E g.form h φ a F z i j α ∂lebesgueC n) := by
  classical
  let P := weightedTwoPairing E g.form h φ u (twoFormPushforward E a F)
  let Q := fun z => (1 / 2 : ℂ) * ∑ i, ∑ j, ∑ α,
    star (coefficients (r := r) E u a z ![i,j] α) * chartTwoDual E g.form h φ a F z i j α
  have hP := weightedTwoPairing_twoFormPushforward_integrable E g μ hμ h hh φ hφ hE u hu a F hF hc hs hskew
  have hPzero (x : M.Carrier) (hx : x ∉ bundleChartSource (r := r) E a) : P x = 0 := by
    apply weightedTwoPairing_eq_zero_of_right_zero
    change (if hy : x ∈ bundleChartSource (r := r) E a then _ else _) = _
    exact dite_eq_right hx
  have hFzero (z : ComplexVector n) (hz : z ∉ localDomain (r := r) E a) : F z = 0 := by
    by_contra hn
    exact hz (hs (subset_tsupport F hn))
  have hQzero (z : ComplexVector n) (hz : z ∉ localDomain (r := r) E a) : Q z = 0 := by
    simp [Q, chartTwoDual, hFzero z hz, Matrix.mulVec, dotProduct]
  have hi : (∫ x, P x ∂μ) = (2 : ℝ) ^ n • ∫ z, Q z ∂lebesgueC n := by
    apply integral_of_compact_chart_density g μ hμ a P Q hP
      (fun x hx => hPzero x (fun hy => hx hy.1))
      (fun z hz => hQzero z (fun hy => hz hy.1))
    intro z hz
    by_cases hzo : z ∈ localDomain (r := r) E a
    · exact weightedTwoPairing_twoFormPushforward_density E g.form h φ u a F hskew z hzo
    · rw [hPzero (chartInv a z) (fun hy => hzo ⟨hz, hy.2⟩), hQzero z hzo]
      simp
  rw [hi]
  apply congrArg (fun c : ℂ => (2 : ℝ) ^ n • c)
  rw [show (∫ z, Q z ∂lebesgueC n) =
    (1 / 2 : ℂ) * ∫ z, (∑ i, ∑ j, ∑ α,
      star (coefficients (r := r) E u a z ![i,j] α) * chartTwoDual E g.form h φ a F z i j α)
        ∂lebesgueC n from integral_const_mul _ _]
  congr 1
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum _ (fun α _ => chartTwoDual_conjugate_test_integrable
        E g h hh φ hφ u hu a F hF hc hs i j α)
    · intro j _
      exact integrable_finsetSum _ (fun α _ => chartTwoDual_conjugate_test_integrable
        E g h hh φ hφ u hu a F hF hc hs i j α)
  · intro i _
    exact integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun α _ =>
      chartTwoDual_conjugate_test_integrable E g h hh φ hφ u hu a F hF hc hs i j α))

end Yau.LeafProofs.L14Aux
