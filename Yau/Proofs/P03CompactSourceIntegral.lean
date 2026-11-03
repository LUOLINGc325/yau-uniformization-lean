import Yau.Proofs.P03InverseCurvatureSupport
import Yau.Proofs.P03CompactInverseCurvature
import Yau.Proofs.P03CompactWeightBounds

open scoped Manifold Topology ContDiff ENNReal
open Set MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The actual variational inverse-curvature integral has one finite bound
before all indices, from a compact smooth source and the proved uniform
pointwise estimates. No real integral is used as a finiteness surrogate. -/
theorem exists_uniform_inverseCurvatureIntegral_bound (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : ℕ → M.Carrier → ℝ) (hN : ∀ j, WeightedNakanoNonnegative (r := r) E h (φ j))
    (f : NQForm E 1) (hf : SmoothForm (r := r) E f)
    {K : Set M.Carrier} (hK : IsCompact K) (hsupp : {x | f x ≠ (0 : NQForm E 1) x} ⊆ K)
    (lam : ℝ) (hlam : 0 < lam)
    (hinv : ∀ j x, x ∈ K → inverseCurvatureNormSq (r := r) E g.form h (φ j) f x ≤
      ENNReal.ofReal (lam⁻¹ * BundleDbar.formNormSq (r := r) E g.form h f x))
    (B : ℝ) (hB : 0 ≤ B) (hweight : ∀ j x, x ∈ K → Real.exp (-φ j x) ≤ B) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ j, inverseCurvatureIntegral (r := r) E g.form h μ (φ j) f ≤ ENNReal.ofReal D := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
    (formNormSq_one_continuous E g h hh f hf).continuousOn
  let A0 := max A 0
  have hA0 : 0 ≤ A0 := le_max_right _ _
  have hnorm (x : M.Carrier) (hx : x ∈ K) :
      BundleDbar.formNormSq (r := r) E g.form h f x ≤ A0 := by
    have ha := hA x hx
    change |BundleDbar.formNormSq (r := r) E g.form h f x| ≤ A at ha
    exact (le_abs_self _).trans (ha.trans (le_max_left _ _))
  let C := lam⁻¹ * A0 * B
  have hfactor : 0 ≤ lam⁻¹ * A0 := mul_nonneg (inv_nonneg.mpr hlam.le) hA0
  have hC : 0 ≤ C := mul_nonneg hfactor hB
  have hmass : μ K < ⊤ := hK.measure_lt_top
  let T : ℝ≥0∞ := ENNReal.ofReal C * μ K
  have hT : T < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass
  refine ⟨T.toReal + 1, by linarith [ENNReal.toReal_nonneg (a := T)], ?_⟩
  intro j
  have hpoint (x : M.Carrier) :
      inverseCurvatureNormSq (r := r) E g.form h (φ j) f x * ENNReal.ofReal (Real.exp (-φ j x)) ≤
        K.indicator (fun _ => ENNReal.ofReal C) x := by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      have hi : inverseCurvatureNormSq (r := r) E g.form h (φ j) f x ≤ ENNReal.ofReal (lam⁻¹ * A0) :=
        (hinv j x hx).trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hnorm x hx) (inv_nonneg.mpr hlam.le)))
      have hw := ENNReal.ofReal_le_ofReal (hweight j x hx)
      have hm := mul_le_mul' hi hw
      simpa only [← ENNReal.ofReal_mul hfactor] using hm
    · rw [indicator_of_notMem hx]
      have hf0 : f x = (0 : NQForm E 1) x := by
        by_contra hne
        exact hx (hsupp hne)
      rw [inverseCurvatureNormSq_zero_at E g.form h (φ j) (hN j) f x hf0, zero_mul]
  calc
    inverseCurvatureIntegral (r := r) E g.form h μ (φ j) f ≤
        ∫⁻ x, K.indicator (fun _ => ENNReal.ofReal C) x ∂μ := lintegral_mono hpoint
    _ = T := lintegral_indicator_const hK.measurableSet _
    _ = ENNReal.ofReal T.toReal := (ENNReal.ofReal_toReal hT.ne).symm
    _ ≤ ENNReal.ofReal (T.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)

end Yau.NodeProofs.P03Aux
