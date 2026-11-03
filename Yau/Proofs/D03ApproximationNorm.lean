import Yau.Proofs.D03ApproximationTail

noncomputable section

open MeasureTheory Filter Set Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.D03Aux
open Yau Yau.BundleDbar Yau.Blueprint.BundlePresentation

section FiberNorm
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem hermitianNormSq_neg (h : HermitianInnerProduct V) (v : V) :
    hermitianNormSq h (-v) = hermitianNormSq h v := by
  simpa only [neg_one_smul, Complex.normSq_neg, Complex.normSq_one, one_mul] using
    B01Aux.hermitianNormSq_smul h (-1) v

theorem hermitianNormSq_real_smul (h : HermitianInnerProduct V) (a : ℝ) (v : V) :
    hermitianNormSq h ((a : ℂ) • v) = a ^ 2 * hermitianNormSq h v := by
  rw [B01Aux.hermitianNormSq_smul]
  simp only [Complex.normSq_ofReal, pow_two]

theorem hermitianNormSq_sub_le (h : HermitianInnerProduct V) (u v : V) :
    hermitianNormSq h (u - v) ≤ 2 * hermitianNormSq h u + 2 * hermitianNormSq h v := by
  have ht : hermitianNormSq h (u + -v) ≤
      2 * hermitianNormSq h u + 2 * hermitianNormSq h (-v) :=
    Yau.LeafProofs.L14Aux.hermitian_add_self_le h u (-v)
  simpa only [sub_eq_add_neg, hermitianNormSq_neg] using ht
end FiberNorm

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A squared triangle integral estimate uses genuine measurability of its
first summand. No subadditivity of lower integrals is silently assumed. -/
theorem sectionIntegral_add_le
    (c : DiscCoordinate M) (k : BundleDbar.Metric E) (u v : Section E)
    (hu : AEMeasurable (fun x => hermitianNormSq (k x) (u x))
      (Yau.Blueprint.BundlePresentation.discArea c)) :
    sectionIntegral E c k (fun x => u x + v x) ≤
      2 * sectionIntegral E c k u + 2 * sectionIntegral E c k v := by
  have hpoint (x : M.Carrier) : ENNReal.ofReal (hermitianNormSq (k x) (u x + v x)) ≤
      2 * ENNReal.ofReal (hermitianNormSq (k x) (u x)) +
        2 * ENNReal.ofReal (hermitianNormSq (k x) (v x)) := by
    have ht : hermitianNormSq (k x) (u x + v x) ≤
        2 * hermitianNormSq (k x) (u x) + 2 * hermitianNormSq (k x) (v x) :=
      Yau.LeafProofs.L14Aux.hermitian_add_self_le (k x) (u x) (v x)
    have hp := ENNReal.ofReal_le_ofReal ht
    rw [ENNReal.ofReal_add
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hermitianNormSq_nonneg (k x) (u x)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hermitianNormSq_nonneg (k x) (v x))),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at hp
    exact hp
  calc
    _ ≤ ∫⁻ x, 2 * ENNReal.ofReal (hermitianNormSq (k x) (u x)) +
        2 * ENNReal.ofReal (hermitianNormSq (k x) (v x))
        ∂Yau.Blueprint.BundlePresentation.discArea c := lintegral_mono hpoint
    _ = _ := by
      have hAu : AEMeasurable (fun x => (2 : ℝ≥0∞) *
          ENNReal.ofReal (hermitianNormSq (k x) (u x)))
          (Yau.Blueprint.BundlePresentation.discArea c) :=
        (ENNReal.measurable_ofReal.comp_aemeasurable hu).const_mul 2
      rw [lintegral_add_left' hAu,
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      rfl

theorem sectionIntegral_neg (c : DiscCoordinate M) (k : BundleDbar.Metric E) (v : Section E) :
    sectionIntegral E c k (fun x => -v x) = sectionIntegral E c k v := by
  apply lintegral_congr
  intro x
  rw [hermitianNormSq_neg]

/-- The cutoff error vanishes outside the actual shrinking tail. -/
def cutoffError (c : DiscCoordinate M) (s : Section E) (n : ℕ) : Section E :=
  fun x => ((cutoff c n x - 1 : ℝ) : ℂ) • s x

theorem cutoffError_normSq (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (s : Section E) (n : ℕ) (x : M.Carrier) :
    hermitianNormSq (k x) (cutoffError E c s n x) =
      (cutoff c n x - 1) ^ 2 * hermitianNormSq (k x) (s x) :=
  hermitianNormSq_real_smul (k x) _ _

theorem cutoffError_normSq_aemeasurable
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (hk : BundleDbar.SmoothMetric (r := r) E k) (s : Section E)
    (hs : HolomorphicSection (r := r) E s) (n : ℕ) :
    AEMeasurable (fun x => hermitianNormSq (k x) (cutoffError E c s n x))
      (Yau.Blueprint.BundlePresentation.discArea c) := by
  have hχ : Continuous (fun x : M.Carrier => (cutoff c n x - 1) ^ 2) :=
    ((Yau.LeafProofs.L18Aux.continuous_of_smoothFn (cutoff_smooth c hc n)).sub continuous_const).pow 2
  have hm := hχ.measurable.aemeasurable.mul (sectionNormSq_aemeasurable E c hc k hk s hs)
  apply hm.congr
  exact Eventually.of_forall (fun x => (cutoffError_normSq E c k s n x).symm)

theorem cutoffError_integral_le_tail
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (s : Section E) (n : ℕ) :
    sectionIntegral E c k (cutoffError E c s n) ≤ sourceTailMass E c k s n := by
  calc
    _ ≤ ∫⁻ x, (sourceTail c n).indicator
        (fun x => ENNReal.ofReal (hermitianNormSq (k x) (s x))) x
        ∂Yau.Blueprint.BundlePresentation.discArea c := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : x ∈ sourceTail c n
      · rw [indicator_of_mem hx]
        apply ENNReal.ofReal_le_ofReal
        rw [cutoffError_normSq]
        have hχ0 := cutoff_nonneg c n x
        have hχ1 := cutoff_le_one c n x
        have hsq : (cutoff c n x - 1) ^ 2 ≤ 1 := by nlinarith
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hsq (hermitianNormSq_nonneg (k x) (s x))
      · rw [indicator_of_notMem hx, cutoffError_normSq,
          cutoff_eq_one c hc n x (le_of_not_gt hx)]
        simp
    _ = _ := lintegral_indicator (sourceTail_measurableSet c hc n) _

theorem sectionIntegral_le_correctionWeightedNorm
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (v : Section E) (n : ℕ) :
    sectionIntegral E c k v ≤ correctionWeightedNorm E c k v n := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  exact le_mul_of_one_le_right (hermitianNormSq_nonneg (k x) (v x)) (weight_power_ge_one c hc n x)

end Yau.Proofs.D03Aux
