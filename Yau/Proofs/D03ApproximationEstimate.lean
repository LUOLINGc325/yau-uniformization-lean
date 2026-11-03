import Yau.Proofs.D03RadialBounds
import Yau.Proofs.B01
import Yau.LeafProofs.L14Exact

noncomputable section

open MeasureTheory Filter Set Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.D03Aux
open Yau Yau.BundleDbar Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The original section mass on the actual moving source annulus. -/
def sourceAnnulusMass (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (s : Section E) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in sourceAnnulus c n, ENNReal.ofReal (hermitianNormSq (k x) (s x))
    ∂Yau.Blueprint.BundlePresentation.discArea c

/-- The power-weighted norm of the same recovered coefficient section. -/
def correctionWeightedNorm (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (v : Section E) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (hermitianNormSq (k x) (v x) *
    ‖c x‖ ^ (-(2 / correctionParameter n))) ∂Yau.Blueprint.BundlePresentation.discArea c

theorem sourceAnnulusMass_le (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (s : Section E) (n : ℕ) : sourceAnnulusMass E c k s n ≤ sectionIntegral E c k s :=
  lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)

/-- The scalar inverse-curvature source bound is localized to the same annulus
and uses the specified intrinsic Hermitian norm. -/
theorem cutoff_source_lintegral_bound
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (s : Section E) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal
      (hermitianNormSq (k x) (s x) * ‖discDbarScalar c (cutoff c n) x‖ ^ 2 /
        discLeviScalar c (weight c n) x * Real.exp (-weight c n x))
        ∂Yau.Blueprint.BundlePresentation.discArea c) ≤
      ENNReal.ofReal (cutoffWeightConstant * Real.exp 6) * sourceAnnulusMass E c k s n := by
  have hpoint (x : M.Carrier) : ENNReal.ofReal
      (hermitianNormSq (k x) (s x) * ‖discDbarScalar c (cutoff c n) x‖ ^ 2 /
        discLeviScalar c (weight c n) x * Real.exp (-weight c n x)) ≤
      (sourceAnnulus c n).indicator
        (fun x => ENNReal.ofReal (cutoffWeightConstant * Real.exp 6) *
          ENNReal.ofReal (hermitianNormSq (k x) (s x))) x := by
    have hnonneg := hermitianNormSq_nonneg (k x) (s x)
    have hscalar := cutoff_inverse_weighted_bound c hc n x
    by_cases hx : x ∈ sourceAnnulus c n
    · rw [indicator_of_mem hx] at hscalar ⊢
      rw [← ENNReal.ofReal_mul (mul_nonneg cutoffWeightConstant_pos.le (Real.exp_pos _).le)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = hermitianNormSq (k x) (s x) *
            (‖discDbarScalar c (cutoff c n) x‖ ^ 2 /
              discLeviScalar c (weight c n) x * Real.exp (-weight c n x)) := by ring
        _ ≤ hermitianNormSq (k x) (s x) * (cutoffWeightConstant * Real.exp 6) :=
          mul_le_mul_of_nonneg_left hscalar hnonneg
        _ = _ := mul_comm _ _
    · rw [indicator_of_notMem hx, discDbarScalar_cutoff_eq_zero_off_annulus c hc n x hx]
      simp
  calc
    _ ≤ ∫⁻ x, (sourceAnnulus c n).indicator
        (fun x => ENNReal.ofReal (cutoffWeightConstant * Real.exp 6) *
          ENNReal.ofReal (hermitianNormSq (k x) (s x))) x
        ∂Yau.Blueprint.BundlePresentation.discArea c := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_indicator (sourceAnnulus_measurableSet c hc n),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

/-- Removing the bounded exponential factor costs precisely exp(1). -/
theorem correctionWeightedNorm_le_exponential_norm
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (v : Section E) (n : ℕ) :
    correctionWeightedNorm E c k v n ≤ ENNReal.ofReal (Real.exp 1) *
      (∫⁻ x, ENNReal.ofReal (hermitianNormSq (k x) (v x) * Real.exp (-weight c n x))
        ∂Yau.Blueprint.BundlePresentation.discArea c) := by
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hweight (x : M.Carrier) : ‖c x‖ ^ (-(2 / correctionParameter n)) ≤
      Real.exp 1 * Real.exp (-weight c n x) := by
    rw [weight_exp_neg c hc n x]
    have hpower := Real.rpow_nonneg (norm_nonneg (c x)) (-(2 / correctionParameter n))
    calc
      _ = Real.exp 1 * (‖c x‖ ^ (-(2 / correctionParameter n)) * Real.exp (-1)) := by
        calc
          _ = ‖c x‖ ^ (-(2 / correctionParameter n)) * (Real.exp 1 * Real.exp (-1)) := by rw [he, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (weight_power_exp_bounds c hc n x).1 hpower) (Real.exp_pos _).le
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp 1) *
        ENNReal.ofReal (hermitianNormSq (k x) (v x) * Real.exp (-weight c n x))
        ∂Yau.Blueprint.BundlePresentation.discArea c := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ hermitianNormSq (k x) (v x) * (Real.exp 1 * Real.exp (-weight c n x)) :=
          mul_le_mul_of_nonneg_left (hweight x) (hermitianNormSq_nonneg _ _)
        _ = _ := by ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The actual L14 solution and its unique coefficient section satisfy the
power-weight bound. The source, weak solution, metric and recovered coefficient
are the very same witnesses throughout both B01 estimate identities. -/
theorem exists_cutoff_correction
    (hSolve : Yau.LeafCandidates.WeightedDbarEstimate (r := r) E)
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : BundleDbar.Metric E) (hE : Holomorphic (r := r) E)
    (hk : BundleDbar.SmoothMetric (r := r) E k)
    (hG : GriffithsNonnegative (r := r) E k)
    (s : Section E) (hs : HolomorphicSection (r := r) E s)
    (hInt : sectionIntegral E c k s < ⊤) (n : ℕ) :
    ∃ f : NQForm E 1, ∃ u : NQForm E 0, ∃ v : Section E,
      IsCutoffSourceForm E c s (cutoff c n) f ∧
      WeightedL2 (r := r) E g.form k μ (weight c n) u ∧
      WeakDbar (r := r) E u f ∧ IsSectionTopForm E c v u ∧
      correctionWeightedNorm E c k v n ≤
        ENNReal.ofReal cutoffSmallConstant * sourceAnnulusMass E c k s n ∧
      correctionWeightedNorm E c k v n < ⊤ := by
  have hg : MetricSmooth g.form := Yau.LeafProofs.L18Aux.metricSmooth_of_smoothMetric g
  have hφ := weight_smooth c hc n
  have hχ := cutoff_smooth c hc n
  have hlevi := discLeviScalar_weight_pos c hc n
  obtain ⟨f, hf, _, hfclosed⟩ := B01Aux.cutoffSourceFormRealization (r := r) E c hc hE s (cutoff c n) hs hχ
  have hbound : inverseCurvatureIntegral (r := r) E g.form k μ (weight c n) f ≤
      2 * (ENNReal.ofReal (cutoffWeightConstant * Real.exp 6) * sourceAnnulusMass E c k s n) :=
    (B01Aux.cutoffInverseCurvatureBound (r := r) E c hc g.form μ k (weight c n)
      (cutoff c n) hg hμ hE hk hG hφ hχ hlevi s f hs hf).trans
      (mul_le_mul_right (cutoff_source_lintegral_bound E c hc k s n) 2)
  have hmass : sourceAnnulusMass E c k s n < ⊤ := (sourceAnnulusMass_le E c k s n).trans_lt hInt
  have hfinite : inverseCurvatureIntegral (r := r) E g.form k μ (weight c n) f < ⊤ :=
    hbound.trans_lt (ENNReal.mul_lt_top (by norm_num)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass))
  have hN := B01Aux.curveWeightedNakanoTransport (r := r) E c hc k (weight c n)
    hE hk hG hφ (fun x => (hlevi x).le)
  obtain ⟨u, huL2, huWeak, huBound⟩ := hSolve g μ k (weight c n) hμ hE hk hφ hN f hfclosed hfinite
  obtain ⟨v, hv, _⟩ := B01Aux.topFormSectionRecovery E c hc u
  have hnorm := B01Aux.sectionTopFormVolumeTransport (r := r) E c hc g.form μ k
    (weight c n) hg hμ hE hk hφ v u huL2.1 hv
  have htwo : (2 : ℝ≥0∞) *
      (∫⁻ x, ENNReal.ofReal (hermitianNormSq (k x) (v x) * Real.exp (-weight c n x))
        ∂Yau.Blueprint.BundlePresentation.discArea c) ≤
      2 * (ENNReal.ofReal (cutoffWeightConstant * Real.exp 6) * sourceAnnulusMass E c k s n) := by
    rw [← hnorm]
    exact huBound.trans hbound
  have hnormBound := (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp htwo
  have hsmall : ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (cutoffWeightConstant * Real.exp 6) =
      ENNReal.ofReal cutoffSmallConstant := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    unfold cutoffSmallConstant
    calc
      Real.exp 1 * (cutoffWeightConstant * Real.exp 6) = (Real.exp 1 * Real.exp 6) * cutoffWeightConstant := by ring
      _ = _ := by rw [← Real.exp_add]; norm_num
  have hvBound : correctionWeightedNorm E c k v n ≤
      ENNReal.ofReal cutoffSmallConstant * sourceAnnulusMass E c k s n := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp 1) * _ := correctionWeightedNorm_le_exponential_norm E c hc k v n
      _ ≤ ENNReal.ofReal (Real.exp 1) *
          (ENNReal.ofReal (cutoffWeightConstant * Real.exp 6) * sourceAnnulusMass E c k s n) :=
        mul_le_mul_right hnormBound _
      _ = _ := by rw [← mul_assoc, hsmall]
  exact ⟨f, u, v, hf, huL2, huWeak, hv, hvBound,
    hvBound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass)⟩

end Yau.Proofs.D03Aux
