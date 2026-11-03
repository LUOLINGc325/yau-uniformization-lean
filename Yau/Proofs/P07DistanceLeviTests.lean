import Yau.Proofs.P07DistanceLeviCalculus

/-! The literal compact-test integrability obligations for continuous
potentials and continuous variable Hermitian upper fields. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L18Aux L22Aux P06Aux

variable {n : ℕ}

theorem continuous_leviDirection_test {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : ComplexVector n) :
    Continuous (fun z => leviDirection (leviC φ z) v) := by
  have hD (w : ComplexVector n) : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z w) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDD (w : ComplexVector n) : Continuous (directionSecond φ w) :=
    (((hD w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
  have heq : (fun z => leviDirection (leviC φ z) v) =
      (fun z => (directionSecond φ v z + directionSecond φ (Complex.I • v) z) / 4) := by
    funext z
    exact leviDirection_eq_second (hφ.contDiffAt.of_le (by simp)) v
  rw [heq]
  exact ((hDD v).add (hDD (Complex.I • v))).div_const 4

theorem tsupport_leviDirection_test_subset {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (v : ComplexVector n) :
    tsupport (fun z => leviDirection (leviC φ z) v) ⊆ tsupport φ := by
  have hDD (w : ComplexVector n) : tsupport (directionSecond φ w) ⊆ tsupport φ :=
    (tsupport_fderiv_apply_subset ℝ w).trans (tsupport_fderiv_apply_subset ℝ w)
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra hzφ
  have hzero (w : ComplexVector n) : directionSecond φ w z = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hzφ (hDD w h))
  have H := leviDirection_eq_second (z := z) (hφ.contDiffAt.of_le (by simp)) v
  rw [hzero, hzero, zero_add, zero_div] at H
  exact hz H

theorem hasCompactSupport_leviDirection_test {φ : ComplexVector n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (v : ComplexVector n) :
    HasCompactSupport (fun z => leviDirection (leviC φ z) v) :=
  hcφ.of_isClosed_subset isClosed_closure (tsupport_leviDirection_test_subset hφ v)

/-- Both integrability clauses use only continuity on the open chart and
the actual compact support of the differentiated test. -/
theorem compactTest_integrability {O : Set (ComplexVector n)} (hO : IsOpen O)
    {f : ComplexVector n → ℝ} {H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ}
    (hf : ContinuousOn f O) (v : ComplexVector n)
    (hH : ContinuousOn (fun z => leviDirection (H z) v) O)
    {φ : ComplexVector n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) (hφO : tsupport φ ⊆ O) :
    Integrable (fun z => f z * leviDirection (leviC φ z) v) (lebesgueC n) ∧
      Integrable (fun z => φ z * leviDirection (H z) v) (lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  constructor
  · have H := integrable_compactTest_mul (lebesgueC n) hO
      (continuous_leviDirection_test hφ v) (hasCompactSupport_leviDirection_test hφ hcφ v)
      ((tsupport_leviDirection_test_subset hφ v).trans hφO) hf
    simpa only [mul_comm] using H
  · exact integrable_compactTest_mul (lebesgueC n) hO hφ.continuous hcφ hφO hH

end Yau.NodeProofs.P07DistanceLevi
