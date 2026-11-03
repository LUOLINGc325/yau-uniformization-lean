import Yau.Geometry.Calculus

open scoped ENNReal Topology
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

def realONB (n : ℕ) : OrthonormalBasis (RIdx n) ℝ (ComplexVector n) :=
  (Pi.orthonormalBasis fun _ : Fin n => Complex.orthonormalBasisOneI).reindex
    (Equiv.sigmaEquivProd (Fin n) (Fin 2))

theorem realONB_apply (n : ℕ) (a : RIdx n) : realONB n a = realVec a := by
  rcases a with ⟨i, j⟩
  fin_cases j <;> ext l <;>
    simp [realONB, OrthonormalBasis.reindex_apply, Pi.orthonormalBasis_apply,
      Complex.coe_orthonormalBasisOneI, realVec, EuclideanSpace.single,
      PiLp.single_apply, smul_eq_mul]

/-- The measure in the actual weak dbar contract is the native real volume,
including in dimension zero. -/
theorem actualMeasure_eq_volume (n : ℕ) :
    lebesgueC n = (volume : Measure (ComplexVector n)) := by
  let b := realONB n
  have hsum : (fun r : RIdx n → ℝ => ∑ a, r a • realVec a) =
      b.repr.symm ∘ (WithLp.toLp 2 :
        (RIdx n → ℝ) → EuclideanSpace ℝ (RIdx n)) := by
    funext r
    simpa only [Function.comp_apply, realONB_apply, PiLp.toLp_apply, b]
      using b.sum_repr_symm (WithLp.toLp 2 r)
  have hmp := b.measurePreserving_repr_symm.comp
    (PiLp.volume_preserving_toLp (RIdx n))
  simpa only [lebesgueC, hsum] using hmp.map_eq

theorem integrable_indicator_of_compact_memLp {n : ℕ}
    {u : ComplexVector n → ℂ} (K : Set (ComplexVector n)) (hK : IsCompact K)
    (hu : MemLp u 2 ((volume : Measure (ComplexVector n)).restrict K)) :
    Integrable (K.indicator u) volume := by
  letI : IsFiniteMeasure ((volume : Measure (ComplexVector n)).restrict K) :=
    ⟨by simpa using hK.measure_lt_top⟩
  exact (integrable_indicator_iff hK.measurableSet).mpr (hu.integrable (by norm_num))

theorem memLp_two_of_lintegral_norm_sq_lt_top {A : Type*} [MeasurableSpace A]
    {μ : Measure A} {f : A → ℂ} (hm : AEStronglyMeasurable f μ)
    (hf : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ) < ⊤) : MemLp f 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨(hm.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖f x‖)).mpr hf

end Yau.NodeProofs.P03Aux
