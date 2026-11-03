import Yau.Proofs.D03ApproximationDbar
import Yau.Proofs.D03ApproximationNorm

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

/-- One genuine holomorphic approximant, with its own positive exponent and a
quantitative error estimate in the original metric. -/
theorem exists_extra_approximant
    (hSolve : Yau.LeafCandidates.WeightedDbarEstimate (r := r) E)
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : BundleDbar.Metric E) (hE : Holomorphic (r := r) E)
    (hk : BundleDbar.SmoothMetric (r := r) E k)
    (hG : GriffithsNonnegative (r := r) E k)
    (s : Section E) (hs : HolomorphicSection (r := r) E s)
    (hInt : sectionIntegral E c k s < ⊤) (n : ℕ) :
    ∃ b : Section E, HolomorphicSection (r := r) E b ∧
      sectionIntegral E c k b < ⊤ ∧
      weightedSectionIntegral E c k b (Real.exp (-2 * correctionParameter n))
        (2 / correctionParameter n) < ⊤ ∧
      sectionIntegral E c k (fun x => b x - s x) ≤
        (2 * (1 + ENNReal.ofReal cutoffSmallConstant)) * sourceTailMass E c k s n := by
  obtain ⟨f, u, v, hf, huL2, huWeak, hv, hvBound, hvFinite⟩ :=
    exists_cutoff_correction E hSolve c hc g μ hμ k hE hk hG s hs hInt n
  have hfEq := B01Aux.cutoffSourceForm_eq E c s (cutoff c n) f hf
  have hu : WeakDbar (r := r) E u (B01Aux.cutoffSourceForm E c s (cutoff c n)) := by
    simpa only [hfEq] using huWeak
  obtain ⟨b, hb, hbAE⟩ := exists_holomorphic_cutoff_difference E c hc hE g μ hμ s hs n u v hu hv
  have hIv : sectionIntegral E c k v ≤
      ENNReal.ofReal cutoffSmallConstant * sourceTailMass E c k s n :=
    (sectionIntegral_le_correctionWeightedNorm E c hc k v n).trans
      (hvBound.trans (mul_le_mul_right (sourceAnnulusMass_le_tail E c k s n)
        (ENNReal.ofReal cutoffSmallConstant)))
  have herrorEq : sectionIntegral E c k (fun x => b x - s x) =
      sectionIntegral E c k (fun x => cutoffError E c s n x + -v x) := by
    apply lintegral_congr_ae
    filter_upwards [hbAE] with x hx
    apply congrArg ENNReal.ofReal
    apply congrArg (hermitianNormSq (k x))
    rw [hx]
    simp only [cutoffError, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  have hError : sectionIntegral E c k (fun x => b x - s x) ≤
      (2 * (1 + ENNReal.ofReal cutoffSmallConstant)) * sourceTailMass E c k s n := by
    calc
      _ = sectionIntegral E c k (fun x => cutoffError E c s n x + -v x) := herrorEq
      _ ≤ 2 * sectionIntegral E c k (cutoffError E c s n) +
          2 * sectionIntegral E c k (fun x => -v x) :=
        sectionIntegral_add_le E c k _ _ (cutoffError_normSq_aemeasurable E c hc k hk s hs n)
      _ = 2 * sectionIntegral E c k (cutoffError E c s n) + 2 * sectionIntegral E c k v := by
        rw [sectionIntegral_neg]
      _ ≤ 2 * sourceTailMass E c k s n +
          2 * (ENNReal.ofReal cutoffSmallConstant * sourceTailMass E c k s n) :=
        add_le_add (mul_le_mul_right (cutoffError_integral_le_tail E c hc k s n) 2)
          (mul_le_mul_right hIv 2)
      _ = _ := by ring
  have htailFinite : sourceTailMass E c k s n < ⊤ := (sourceTailMass_le E c k s n).trans_lt hInt
  have hconstantFinite : (2 : ℝ≥0∞) * (1 + ENNReal.ofReal cutoffSmallConstant) < ⊤ :=
    ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.ofReal_lt_top⟩)
  have hErrorFinite : sectionIntegral E c k (fun x => b x - s x) < ⊤ :=
    hError.trans_lt (ENNReal.mul_lt_top hconstantFinite htailFinite)
  have hbFinite : sectionIntegral E c k b < ⊤ := by
    have ht := sectionIntegral_add_le E c k s (fun x => b x - s x)
      (sectionNormSq_aemeasurable E c hc k hk s hs)
    have heq : (fun x => s x + (b x - s x)) = b := by funext x; abel
    rw [heq] at ht
    exact ht.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) hInt,
      ENNReal.mul_lt_top (by norm_num) hErrorFinite⟩)
  have hdomain : MeasurableSet {x : M.Carrier | 0 < ‖c x‖ ∧
      ‖c x‖ < Real.exp (-2 * correctionParameter n)} :=
    ((isOpen_lt continuous_const (B01Aux.disc_continuous c hc).norm).inter
      (isOpen_lt (B01Aux.disc_continuous c hc).norm continuous_const)).measurableSet
  have hExtra : weightedSectionIntegral E c k b (Real.exp (-2 * correctionParameter n))
      (2 / correctionParameter n) ≤ correctionWeightedNorm E c k v n := by
    calc
      _ = ∫⁻ x in {x : M.Carrier | 0 < ‖c x‖ ∧ ‖c x‖ < Real.exp (-2 * correctionParameter n)},
          ENNReal.ofReal (hermitianNormSq (k x) (v x) * ‖c x‖ ^ (-(2 / correctionParameter n)))
          ∂Yau.Blueprint.BundlePresentation.discArea c := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae hbAE, ae_restrict_mem hdomain] with x hx hxd
        have hχ : cutoff c n x = 0 := cutoff_eq_zero c hc n x hxd.2.le
        have hbx : b x = -v x := by simpa only [hχ, Complex.ofReal_zero, zero_smul, zero_sub] using hx
        rw [hbx, hermitianNormSq_neg]
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
  exact ⟨b, hb, hbFinite, hExtra.trans_lt hvFinite, hError⟩

/-- The paper's full approximation sequence. Its sections live in the original
bundle and converge in the original Hermitian L² integral. -/
theorem exists_extra_approximants
    (hSolve : Yau.LeafCandidates.WeightedDbarEstimate (r := r) E)
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (k : BundleDbar.Metric E) (hE : Holomorphic (r := r) E)
    (hk : BundleDbar.SmoothMetric (r := r) E k)
    (hG : GriffithsNonnegative (r := r) E k)
    (s : Section E) (hs : HolomorphicSection (r := r) E s)
    (hInt : sectionIntegral E c k s < ⊤) :
    ∃ b : ℕ → Section E,
      (∀ n, HolomorphicSection (r := r) E (b n)) ∧
      (∀ n, sectionIntegral E c k (b n) < ⊤) ∧
      (∀ n, weightedSectionIntegral E c k (b n) (Real.exp (-2 * correctionParameter n))
        (2 / correctionParameter n) < ⊤) ∧
      Tendsto (fun n => sectionIntegral E c k (fun x => b n x - s x)) atTop (𝓝 0) := by
  classical
  choose b hb hbFinite hbExtra hbError using fun n =>
    exists_extra_approximant E hSolve c hc g μ hμ k hE hk hG s hs hInt n
  refine ⟨b, hb, hbFinite, hbExtra, ?_⟩
  have hTail := sourceTailMass_tendsto_zero E c hc k hk s hs hInt
  have hconstant : (2 : ℝ≥0∞) * (1 + ENNReal.ofReal cutoffSmallConstant) ≠ ⊤ :=
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨by norm_num, ENNReal.ofReal_lt_top⟩)).ne
  have hupper : Tendsto
      (fun n => (2 * (1 + ENNReal.ofReal cutoffSmallConstant)) * sourceTailMass E c k s n)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hTail (Or.inr hconstant)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => bot_le) hbError

end Yau.Proofs.D03Aux
