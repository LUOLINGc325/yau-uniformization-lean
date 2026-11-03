import Yau.Proofs.D03Approximation
import Yau.Proofs.D03PlanarRemovable
import Yau.Proofs.B01Image

noncomputable section

open MeasureTheory Filter Set Bundle
open scoped Topology ContDiff Manifold ENNReal

namespace Yau.Proofs.D03Aux
open Yau Yau.BundleDbar Yau.Blueprint.BundlePresentation

/-- A single point has zero ordinary area, for arbitrary nonnegative integrands. -/
theorem lintegral_ball_eq_punctured (R : ℝ) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in Metric.ball (0 : ℂ) R, f z ∂volume) =
      ∫⁻ z in planarPuncturedDisc R, f z ∂volume := by
  have hzero : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by simp [ae_iff]
  have hsets : Metric.ball (0 : ℂ) R =ᵐ[(volume : Measure ℂ)] planarPuncturedDisc R := by
    filter_upwards [hzero] with z hz
    simp [mem_ball_zero_iff, planarPuncturedDisc, norm_pos_iff, hz]
  rw [Measure.restrict_congr_set hsets]

variable {M : ComplexManifold 1} {r q : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Boundedness of the actual bundle map controls the ordinary-area norm of
its actual image, with the same constant and the original section metric. -/
theorem imageSection_l2_bound
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ x v, ‖A x v‖ ^ 2 ≤ C * hermitianNormSq (k x) v) (s : Section E) :
    (∫⁻ z in Yau.Blueprint.puncturedUnitDisc,
      ENNReal.ofReal (‖imageSection E c A s z‖ ^ 2) ∂volume) ≤
      ENNReal.ofReal C * sectionIntegral E c k s := by
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖A x (s x)‖ ^ 2)
        ∂Yau.Blueprint.BundlePresentation.discArea c :=
      (B01Aux.lintegral_discArea c hc _).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (hermitianNormSq (k x) (s x))
        ∂Yau.Blueprint.BundlePresentation.discArea c := by
      apply lintegral_mono
      intro x
      exact (ENNReal.ofReal_le_ofReal (hBound x (s x))).trans_eq (ENNReal.ofReal_mul hC)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The same numerical image bound applies to differences of actual sections. -/
theorem imageSection_difference_l2_bound
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ x v, ‖A x v‖ ^ 2 ≤ C * hermitianNormSq (k x) v)
    (s t : Section E) :
    (∫⁻ z in Yau.Blueprint.puncturedUnitDisc,
      ENNReal.ofReal (‖imageSection E c A s z - imageSection E c A t z‖ ^ 2) ∂volume) ≤
      ENNReal.ofReal C * sectionIntegral E c k (fun x => s x - t x) := by
  have heq (z : ℂ) : imageSection E c A s z - imageSection E c A t z =
      imageSection E c A (fun x => s x - t x) z :=
    ((A (c.symm z)).map_sub (s (c.symm z)) (t (c.symm z))).symm
  simpa only [heq] using imageSection_l2_bound E c hc k A C hC hBound (fun x => s x - t x)

/-- Actual ambient images of finite-norm original holomorphic sections extend
pointwise across zero, by the proved ordinary-area L² removal theorem. -/
theorem exists_image_extension
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (A : MapToTrivial E q) (hE : Holomorphic (r := r) E)
    (hHA : HolomorphicMap (r := r) E A) (hBound : BoundedMap E k A)
    (s : Section E) (hs : HolomorphicSection (r := r) E s)
    (hInt : sectionIntegral E c k s < ⊤) :
    ∃ F : ℂ → ComplexVector q, DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      ∀ z ∈ Yau.Blueprint.puncturedUnitDisc, F z = imageSection E c A s z := by
  obtain ⟨C, hC, hCBound⟩ := hBound
  have hi : (∫⁻ z in Yau.Blueprint.puncturedUnitDisc,
      ENNReal.ofReal (‖imageSection E c A s z‖ ^ 2) ∂volume) < ⊤ :=
    (imageSection_l2_bound E c hc k A C hC hCBound s).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hInt)
  have hHol := (B01Aux.imageSectionTransport (r := r) (q := q) E c hc A hE hHA s hs).1
  obtain ⟨F, hF, hFEq⟩ := exists_holomorphic_l2_extension 1 (by norm_num)
    (imageSection E c A s) hHol hi
  exact ⟨F, hF, fun z hz => hFEq z hz.1 hz.2⟩

/-- Area norm convergence of original sections gives area norm convergence of
these same actual image extensions. No inverse bound or division by C is used. -/
theorem image_extensions_and_l2_convergence
    (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (k : BundleDbar.Metric E)
    (hk : BundleDbar.SmoothMetric (r := r) E k)
    (A : MapToTrivial E q) (hE : Holomorphic (r := r) E)
    (hHA : HolomorphicMap (r := r) E A) (hBound : BoundedMap E k A)
    (s : Section E) (hs : HolomorphicSection (r := r) E s)
    (hInt : sectionIntegral E c k s < ⊤)
    (b : ℕ → Section E) (hb : ∀ n, HolomorphicSection (r := r) E (b n))
    (hbFinite : ∀ n, sectionIntegral E c k (b n) < ⊤)
    (hbConv : Tendsto (fun n => sectionIntegral E c k (fun x => b n x - s x)) atTop (𝓝 0)) :
    ∃ F : ℂ → ComplexVector q, ∃ Fn : ℕ → ℂ → ComplexVector q,
      DifferentiableOn ℂ F (Metric.ball 0 1) ∧
      (∀ n, DifferentiableOn ℂ (Fn n) (Metric.ball 0 1)) ∧
      (∀ z ∈ Yau.Blueprint.puncturedUnitDisc, F z = imageSection E c A s z) ∧
      (∀ n, ∀ z ∈ Yau.Blueprint.puncturedUnitDisc, Fn n z = imageSection E c A (b n) z) ∧
      (∀ n, (∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume) < ⊤) ∧
      Tendsto (fun n => ∫⁻ z in Metric.ball (0 : ℂ) 1,
        ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume) atTop (𝓝 0) := by
  classical
  obtain ⟨F, hF, hFEq⟩ := exists_image_extension E c hc k A hE hHA hBound s hs hInt
  choose Fn hFn hFnEq using fun n => exists_image_extension E c hc k A hE hHA hBound (b n) (hb n) (hbFinite n)
  obtain ⟨C, hC, hCBound⟩ := hBound
  have hmassEq (n : ℕ) : (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume) =
      ∫⁻ z in Yau.Blueprint.puncturedUnitDisc,
        ENNReal.ofReal (‖imageSection E c A (b n) z - imageSection E c A s z‖ ^ 2) ∂volume := by
    rw [lintegral_ball_eq_punctured]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem B01Aux.puncturedUnitDisc_measurableSet] with z hz
    rw [hFnEq n z hz, hFEq z hz]
  have hmassBound (n : ℕ) : (∫⁻ z in Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (‖Fn n z - F z‖ ^ 2) ∂volume) ≤
      ENNReal.ofReal C * sectionIntegral E c k (fun x => b n x - s x) := by
    rw [hmassEq]
    exact imageSection_difference_l2_bound E c hc k A C hC hCBound (b n) s
  have hdiffFinite (n : ℕ) : sectionIntegral E c k (fun x => b n x - s x) < ⊤ := by
    have ht := sectionIntegral_add_le E c k (b n) (fun x => -s x)
      (sectionNormSq_aemeasurable E c hc k hk (b n) (hb n))
    have heq : (fun x => b n x + -s x) = (fun x => b n x - s x) := by funext x; exact (sub_eq_add_neg _ _).symm
    rw [heq, sectionIntegral_neg] at ht
    exact ht.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (hbFinite n),
      ENNReal.mul_lt_top (by norm_num) hInt⟩)
  refine ⟨F, Fn, hF, hFn, hFEq, hFnEq, ?_, ?_⟩
  · intro n
    exact (hmassBound n).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hdiffFinite n))
  · have hupper : Tendsto (fun n => ENNReal.ofReal C * sectionIntegral E c k (fun x => b n x - s x))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hbConv (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => bot_le) hmassBound

end Yau.Proofs.D03Aux
