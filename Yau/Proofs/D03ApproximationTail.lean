import Yau.Proofs.D03ApproximationEstimate
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

noncomputable section

open MeasureTheory Filter Set Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.D03Aux
open Yau Yau.BundleDbar Yau.Blueprint.BundlePresentation
open Yau.LeafProofs.L14Aux

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The original intrinsic norm is measurable for ordinary area; its proof uses
the original frame metric matrix and section coefficients. -/
theorem sectionNormSq_aemeasurable
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (hk : BundleDbar.SmoothMetric (r := r) E k) (s : Section E)
    (hs : HolomorphicSection (r := r) E s) :
    AEMeasurable (fun x => hermitianNormSq (k x) (s x))
      (Yau.Blueprint.BundlePresentation.discArea c) := by
  have hlocal (a : M.Carrier) : ContinuousOn
      (fun z => hermitianNormSq (k (chartInv a z)) (s (chartInv a z)))
      (localDomain (r := r) E a) := by
    have hS := (B01Aux.holomorphic_contDiffOn_one (hs a)
      (localDomain_isOpen (r := r) E a)).continuousOn
    have hSα (α : Fin r) : ContinuousOn
        (fun z => sectionCoefficients (r := r) E s a z α) (localDomain (r := r) E a) :=
      (PiLp.proj 2 (fun _ : Fin r => ℂ) (𝕜 := ℂ) α).continuous.comp_continuousOn hS
    have hsum : ContinuousOn (fun z =>
        (∑ α, ∑ β, star (sectionCoefficients (r := r) E s a z α) *
          BundleDbar.metricMatrix (r := r) E k a z α β *
            sectionCoefficients (r := r) E s a z β).re) (localDomain (r := r) E a) := by
      exact Complex.continuous_re.comp_continuousOn
        (continuousOn_finsetSum Finset.univ fun α _ => continuousOn_finsetSum Finset.univ fun β _ =>
          (((hSα α).star.mul (hk a α β).continuousOn).mul (hSα β)))
    apply hsum.congr
    intro z hz
    exact (congrArg Complex.re (metricMatrix_pairing (r := r) E k a z hz
      (s (chartInv a z)) (s (chartInv a z)))).symm
  have hlarge : AEMeasurable (fun x => hermitianNormSq (k x) (s x))
      ((2 : ℝ≥0∞) • Yau.Blueprint.BundlePresentation.discArea c) := by
    apply aemeasurable_of_bundleCharts (r := r) E (B01Aux.flatDiscField c hc)
      ((2 : ℝ≥0∞) • Yau.Blueprint.BundlePresentation.discArea c) (B01Aux.flatDiscField_volume c hc)
    intro a
    exact (hlocal a).aemeasurable (localDomain_isOpen (r := r) E a).measurableSet
  exact (aemeasurable_smul_measure_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hlarge

/-- The original section mass in the shrinking radial neighbourhood. -/
def sourceTailMass (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (s : Section E) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x in sourceTail c n, ENNReal.ofReal (hermitianNormSq (k x) (s x))
    ∂Yau.Blueprint.BundlePresentation.discArea c

theorem sourceTailMass_le (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (s : Section E) (n : ℕ) : sourceTailMass E c k s n ≤ sectionIntegral E c k s :=
  lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)

theorem sourceAnnulusMass_le_tail (c : DiscCoordinate M) (k : BundleDbar.Metric E)
    (s : Section E) (n : ℕ) : sourceAnnulusMass E c k s n ≤ sourceTailMass E c k s n :=
  lintegral_mono' (Measure.restrict_mono (sourceAnnulus_subset_tail c n) le_rfl) (fun _ => le_rfl)

/-- Shrinking to the deleted origin loses all finite original L² mass. -/
theorem sourceTailMass_tendsto_zero
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (hk : BundleDbar.SmoothMetric (r := r) E k) (s : Section E)
    (hs : HolomorphicSection (r := r) E s) (hInt : sectionIntegral E c k s < ⊤) :
    Tendsto (sourceTailMass E c k s) atTop (𝓝 0) := by
  let F : M.Carrier → ℝ≥0∞ := fun x => ENNReal.ofReal (hermitianNormSq (k x) (s x))
  let Fn : ℕ → M.Carrier → ℝ≥0∞ := fun n => (sourceTail c n).indicator F
  have hF : AEMeasurable F (Yau.Blueprint.BundlePresentation.discArea c) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (sectionNormSq_aemeasurable E c hc k hk s hs)
  have hFn (n : ℕ) : AEMeasurable (Fn n) (Yau.Blueprint.BundlePresentation.discArea c) :=
    hF.indicator (sourceTail_measurableSet c hc n)
  have hbound (n : ℕ) : Fn n ≤ᵐ[Yau.Blueprint.BundlePresentation.discArea c] F := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ sourceTail c n
    · change (sourceTail c n).indicator F x ≤ F x
      rw [indicator_of_mem hx]
    · change (sourceTail c n).indicator F x ≤ F x
      rw [indicator_of_notMem hx]
      exact bot_le
  have hradius : Tendsto (fun n => Real.exp (-correctionParameter n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp correctionParameter_tendsto)
  have hpoint (x : M.Carrier) : Tendsto (fun n => Fn n x) atTop (𝓝 0) := by
    have hsmall : ∀ᶠ n in atTop, Real.exp (-correctionParameter n) < ‖c x‖ :=
      (tendsto_order.1 hradius).2 _ (B01Aux.disc_mem c hc x).1
    have heq : (fun n => Fn n x) =ᶠ[atTop] (fun _ => 0) := by
      filter_upwards [hsmall] with n hn
      apply indicator_of_notMem
      exact fun h => (not_lt_of_ge hn.le) h
    exact (tendsto_congr' heq).mpr tendsto_const_nhds
  have ht := tendsto_lintegral_of_dominated_convergence' F hFn hbound hInt.ne
    (Eventually.of_forall hpoint)
  have hid (n : ℕ) : (∫⁻ a, Fn n a ∂Yau.Blueprint.BundlePresentation.discArea c) =
      sourceTailMass E c k s n := lintegral_indicator (sourceTail_measurableSet c hc n) F
  rw [funext hid] at ht
  simpa only [lintegral_zero] using ht

end Yau.Proofs.D03Aux
