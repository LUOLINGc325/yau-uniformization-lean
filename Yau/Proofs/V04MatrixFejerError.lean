import Yau.Proofs.V04FejerCircleBridge
import Yau.Proofs.V04NegativeSymbol
import Yau.Proofs.V04SequenceTails

/-! The exact frozen Frobenius Fejer error is bounded by the exact
matrix Fourier seminorm. The energy estimate uses finiteness of the
admissible disc before converting any ENNReal expression. -/

open MeasureTheory AddCircle
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

theorem circleAverage_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    circleAverage (fun θ => ∑ i ∈ s, f i θ) = ∑ i ∈ s, circleAverage (f i) := by
  unfold circleAverage
  rw [intervalIntegral.integral_finsetSum (fun i hi => (hf i hi).intervalIntegrable _ _),
    Finset.mul_sum]

variable {n q : ℕ} {X : KahlerManifold n}

theorem matrixFejer_error_ennreal (A : ℝ → CotangentMatrix n)
    (hA : ∀ i k, Continuous (fun θ => A θ i k))
    (hp : ∀ i k, Function.Periodic (fun θ => A θ i k) (2 * Real.pi)) (P : ℕ) :
    ENNReal.ofReal (circleAverage (fun θ => matrixFrobSq (fejerMean A P θ - A θ))) ≤
      ENNReal.ofReal (((P : ℝ) + 1)⁻¹) * matrixDSq A := by
  have havg := circleAverage_finsetSum Finset.univ
    (fun (p : CotangentIndex n × CotangentIndex n) θ =>
      ‖fejerMean A P θ p.1 p.2 - A θ p.1 p.2‖ ^ 2)
    (fun p _ => ((fejerMean_entry_continuous A P p.1 p.2).sub (hA p.1 p.2)).norm.pow 2)
  have havg' : circleAverage (fun θ => matrixFrobSq (fejerMean A P θ - A θ)) =
      ∑ p : CotangentIndex n × CotangentIndex n,
        circleAverage (fun θ => ‖fejerMean A P θ p.1 p.2 - A θ p.1 p.2‖ ^ 2) := by
    simpa only [Fintype.sum_prod_type, Matrix.sub_apply, matrixFrobSq] using havg
  rw [havg', ENNReal.ofReal_sum_of_nonneg (fun p _ => circleAverage_nonneg (fun _ => sq_nonneg _))]
  calc
    _ ≤ ∑ p : CotangentIndex n × CotangentIndex n,
        ENNReal.ofReal (((P : ℝ) + 1)⁻¹) *
          boundaryDSq (fun θ (_ : Unit) => A θ p.1 p.2) :=
      Finset.sum_le_sum (fun p _ => fejerMean_entry_error_ennreal A hA hp P p.1 p.2)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [matrixDSq, boundaryDSq, Finset.univ_unique, Finset.sum_singleton]

theorem matrixFejer_error_real (A : ℝ → CotangentMatrix n)
    (hA : ∀ i k, Continuous (fun θ => A θ i k))
    (hp : ∀ i k, Function.Periodic (fun θ => A θ i k) (2 * Real.pi))
    (hfinite : matrixDSq A ≠ ⊤) (P : ℕ) :
    circleAverage (fun θ => matrixFrobSq (fejerMean A P θ - A θ)) ≤
      (matrixDSq A).toReal / (P + 1) := by
  have hR : ENNReal.ofReal (((P : ℝ) + 1)⁻¹) * matrixDSq A ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  have hh := ENNReal.toReal_mono hR (matrixFejer_error_ennreal A hA hp P)
  have hnon : 0 ≤ circleAverage (fun θ => matrixFrobSq (fejerMean A P θ - A θ)) :=
    circleAverage_nonneg (fun _ =>
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  rw [ENNReal.toReal_ofReal hnon,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ ((P : ℝ) + 1)⁻¹)] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

theorem negativeFejerError_bound {d : VariationData X q} (hd : VariationSetup d)
    {a : ℕ} (ha : 4 ≤ a) (hsymbol : SymbolBounds d a) :
    ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ F E, AdmissibleVariationDisc d j F →
      NormalizedDiscFrame d.G F.f E → ∀ P : ℕ, 0 < P →
        negativeFejerError d j a F E P ≤ C * (1 + (variationEnergy d j F).toReal) / P := by
  intro j
  obtain ⟨C, hC, hbound⟩ := negative_symbol_bounds hd ha hsymbol j
  obtain ⟨CT, _, hT⟩ := hsymbol j
  refine ⟨C, hC, fun F E hF hE P hP => ?_⟩
  let A := fun θ => matrixNegative (boundarySymbol d j a F E (circlePoint θ))
  have hA : ∀ i k, Continuous (fun θ => A θ i k) :=
    matrixNegative_entry_continuous
      (fun i k => (boundarySymbol_trace_contDiff hd j a ha F hF E hE i k).continuous)
      (fun θ => ((hT F E hF hE).1 θ).1)
  have hp : ∀ i k, Function.Periodic (fun θ => A θ i k) (2 * Real.pi) :=
    fun i k => circleTrace_periodic (fun z => matrixNegative (boundarySymbol d j a F E z) i k)
  have hb := (hbound F E hF hE).2
  have he := admissible_energy_finite hF
  have hR : ENNReal.ofReal C * (1 + variationEnergy d j F) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨by simp, he⟩)
  have hf : matrixDSq A ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hb (lt_top_iff_ne_top.mpr hR))
  have hreal := ENNReal.toReal_mono hR hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_add (by simp : (1 : ENNReal) ≠ ⊤) he, ENNReal.toReal_one] at hreal
  have herr := matrixFejer_error_real A hA hp hf P
  have hnum : 0 ≤ C * (1 + (variationEnergy d j F).toReal) :=
    mul_nonneg hC (by positivity)
  exact herr.trans ((div_le_div_of_nonneg_right hreal (by positivity)).trans
    (div_le_div_of_nonneg_left hnum (by exact_mod_cast hP) (by linarith)))

end Yau.Blueprint.V04Proof
