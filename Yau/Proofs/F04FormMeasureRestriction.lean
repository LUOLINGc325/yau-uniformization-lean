import Yau.Proofs.F03ScalarForms

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def completedFormSection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (a : L2FormHilbert g μ k) : RealForm M k :=
  Classical.choose (l2FormHilbert_exists_section g μ a)

theorem completedFormSection_mem (g : SmoothMetric M) (μ : Measure M.Carrier)
    (a : L2FormHilbert g μ k) : L2RealForm g.form μ (completedFormSection g μ a) :=
  (Classical.choose_spec (l2FormHilbert_exists_section g μ a)).choose

theorem completedFormSection_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (a : L2FormHilbert g μ k) :
    realizeL2Form g μ (L2FormSpace.ofSection (completedFormSection g μ a)
      (completedFormSection_mem g μ a)) = a :=
  (Classical.choose_spec (l2FormHilbert_exists_section g μ a)).choose_spec

def formMeasureRestrictionValue (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) (a : L2FormHilbert g μ k) : L2FormHilbert g ν k :=
  realizeL2Form g ν (L2FormSpace.ofSection (completedFormSection g μ a)
    (l2RealForm_mono_measure g.form hνμ (completedFormSection_mem g μ a)))

/-- Every actual representative gives the same restriction. -/
theorem formMeasureRestrictionValue_realize (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    formMeasureRestrictionValue g μ ν hνμ (realizeL2Form g μ (L2FormSpace.ofSection A hA)) =
      realizeL2Form g ν (L2FormSpace.ofSection A (l2RealForm_mono_measure g.form hνμ hA)) := by
  let a := realizeL2Form g μ (L2FormSpace.ofSection A hA)
  let B := completedFormSection g μ a
  have hB : L2RealForm g.form μ B := completedFormSection_mem g μ a
  have he : realizeL2Form g μ (L2FormSpace.ofSection B hB) =
      realizeL2Form g μ (L2FormSpace.ofSection A hA) := completedFormSection_realize g μ a
  have ha : ∀ᵐ x ∂μ, B x = A x :=
    (realizeL2Form_eq_iff_ae g μ (L2FormSpace.ofSection B hB) (L2FormSpace.ofSection A hA)).mp he
  exact (realizeL2Form_eq_iff_ae g ν
    (L2FormSpace.ofSection B (l2RealForm_mono_measure g.form hνμ hB))
    (L2FormSpace.ofSection A (l2RealForm_mono_measure g.form hνμ hA))).mpr
      (ha.filter_mono (ae_mono hνμ))

def formMeasureRestrictionLinear (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) : L2FormHilbert g μ k →ₗ[ℝ] L2FormHilbert g ν k where
  toFun := formMeasureRestrictionValue g μ ν hνμ
  map_add' a b := by
    obtain ⟨A, hA, ha⟩ := l2FormHilbert_exists_section g μ a
    obtain ⟨B, hB, hb⟩ := l2FormHilbert_exists_section g μ b
    have hAB := (l2FormSubmodule g μ k).add_mem hA hB
    rw [← ha, ← hb]
    change formMeasureRestrictionValue g μ ν hνμ
      ((L2FormSpace.ofSection A hA : L2FormHilbert g μ k) +
        (L2FormSpace.ofSection B hB : L2FormHilbert g μ k)) = _
    rw [← UniformSpace.Completion.coe_add]
    change formMeasureRestrictionValue g μ ν hνμ
      (realizeL2Form g μ (L2FormSpace.ofSection (A + B) hAB)) = _
    rw [formMeasureRestrictionValue_realize, formMeasureRestrictionValue_realize,
      formMeasureRestrictionValue_realize]
    exact UniformSpace.Completion.coe_add
      (L2FormSpace.ofSection A (l2RealForm_mono_measure g.form hνμ hA))
      (L2FormSpace.ofSection B (l2RealForm_mono_measure g.form hνμ hB))
  map_smul' c a := by
    obtain ⟨A, hA, ha⟩ := l2FormHilbert_exists_section g μ a
    have hAc := (l2FormSubmodule g μ k).smul_mem c hA
    rw [← ha]
    change formMeasureRestrictionValue g μ ν hνμ
      (c • (L2FormSpace.ofSection A hA : L2FormHilbert g μ k)) = _
    rw [← UniformSpace.Completion.coe_smul]
    change formMeasureRestrictionValue g μ ν hνμ
      (realizeL2Form g μ (L2FormSpace.ofSection (c • A) hAc)) = _
    rw [formMeasureRestrictionValue_realize, formMeasureRestrictionValue_realize]
    exact UniformSpace.Completion.coe_smul c
      (L2FormSpace.ofSection A (l2RealForm_mono_measure g.form hνμ hA))

theorem realizeForm_mono_measure_norm_le (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    ‖realizeL2Form g ν (L2FormSpace.ofSection A (l2RealForm_mono_measure g.form hνμ hA))‖ ≤
      ‖realizeL2Form g μ (L2FormSpace.ofSection A hA)‖ := by
  have hAν : L2RealForm g.form ν A := l2RealForm_mono_measure g.form hνμ hA
  have hν : ‖realizeL2Form g ν (L2FormSpace.ofSection A hAν)‖ ^ 2 =
      ∫ x, formNormSq g.form A x ∂ν :=
    realizeL2Form_norm_sq g ν (L2FormSpace.ofSection A hAν)
  have hμ : ‖realizeL2Form g μ (L2FormSpace.ofSection A hA)‖ ^ 2 =
      ∫ x, formNormSq g.form A x ∂μ :=
    realizeL2Form_norm_sq g μ (L2FormSpace.ofSection A hA)
  have hm : (∫ x, formNormSq g.form A x ∂ν) ≤ ∫ x, formNormSq g.form A x ∂μ :=
    integral_mono_measure hνμ (ae_of_all μ (fun x => formNormSq_nonneg g.form A x))
      (formNormSq_integrable g μ A hA)
  have hs : ‖realizeL2Form g ν (L2FormSpace.ofSection A hAν)‖ ^ 2 ≤
      ‖realizeL2Form g μ (L2FormSpace.ofSection A hA)‖ ^ 2 :=
    hν.le.trans (hm.trans hμ.symm.le)
  nlinarith only [hs, norm_nonneg (realizeL2Form g ν (L2FormSpace.ofSection A hAν)),
    norm_nonneg (realizeL2Form g μ (L2FormSpace.ofSection A hA))]

theorem formMeasureRestrictionLinear_norm_le (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) (a : L2FormHilbert g μ k) :
    ‖formMeasureRestrictionLinear g μ ν hνμ a‖ ≤ ‖a‖ := by
  change ‖formMeasureRestrictionValue g μ ν hνμ a‖ ≤ ‖a‖
  calc
    _ ≤ ‖realizeL2Form g μ (L2FormSpace.ofSection (completedFormSection g μ a)
      (completedFormSection_mem g μ a))‖ :=
        realizeForm_mono_measure_norm_le g μ ν hνμ _ (completedFormSection_mem g μ a)
    _ = ‖a‖ := congrArg norm (completedFormSection_realize g μ a)

/-- Genuine bounded restriction on completed form spaces. Actual section
representatives exist by a proved theorem and the map is independent of their choice. -/
def formMeasureRestriction (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) : L2FormHilbert g μ k →L[ℝ] L2FormHilbert g ν k :=
  (formMeasureRestrictionLinear g μ ν hνμ).mkContinuous 1
    (fun a => by simpa only [one_mul] using formMeasureRestrictionLinear_norm_le g μ ν hνμ a)

theorem formMeasureRestriction_realize (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    formMeasureRestriction g μ ν hνμ (realizeL2Form g μ (L2FormSpace.ofSection A hA)) =
      realizeL2Form g ν (L2FormSpace.ofSection A (l2RealForm_mono_measure g.form hνμ hA)) :=
  formMeasureRestrictionValue_realize g μ ν hνμ A hA

theorem formMeasureRestriction_norm_le (g : SmoothMetric M) (μ ν : Measure M.Carrier)
    (hνμ : ν ≤ μ) (a : L2FormHilbert g μ k) :
    ‖formMeasureRestriction g μ ν hνμ a‖ ≤ ‖a‖ :=
  formMeasureRestrictionLinear_norm_le g μ ν hνμ a

end Yau.F04Proof
