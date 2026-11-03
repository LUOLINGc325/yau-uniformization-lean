import Yau.Proofs.F04FormMultiplierStrong

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def positiveIndicator (s : ℝ) : ℝ := if 0 < s then 1 else 0

theorem positiveIndicator_measurable : Measurable positiveIndicator :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

theorem positiveIndicator_abs_le (s : ℝ) : |positiveIndicator s| ≤ 1 := by
  unfold positiveIndicator
  split_ifs <;> norm_num

theorem positiveIndicator_aestronglyMeasurable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : Lp ℝ 2 μ) :
    AEStronglyMeasurable (fun x => positiveIndicator (f x)) μ :=
  (positiveIndicator_measurable.comp_aemeasurable (Lp.memLp f).aemeasurable).aestronglyMeasurable

def positiveFormMultiplier (g : SmoothMetric M) (μ : Measure M.Carrier) (f : Lp ℝ 2 μ) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ k :=
  multiplyL2FormHilbert g μ (fun x => positiveIndicator (f x))
    (positiveIndicator_aestronglyMeasurable μ f) 1 zero_le_one (fun x => positiveIndicator_abs_le (f x))

theorem positive_active_form_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : Lp ℝ 2 μ) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    L2RealForm g.form μ (fun x => if 0 < f x then A x else 0) := by
  have he : (fun x => if 0 < f x then A x else 0) =
      multiplyRealForm (fun x => positiveIndicator (f x)) A := by
    funext x
    unfold positiveIndicator multiplyRealForm
    split_ifs with hx <;> simp [hx]
  rw [he]
  exact l2RealForm_multiply_bounded g μ _ (positiveIndicator_aestronglyMeasurable μ f)
    1 zero_le_one (fun x => positiveIndicator_abs_le (f x)) A hA

theorem positiveFormMultiplier_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : Lp ℝ 2 μ) (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    positiveFormMultiplier g μ f (realizeL2Form g μ (L2FormSpace.ofSection A hA)) =
      realizeL2Form g μ (L2FormSpace.ofSection (fun x => if 0 < f x then A x else 0)
        (positive_active_form_l2 g μ f A hA)) := by
  unfold positiveFormMultiplier
  rw [multiplyL2FormHilbert_realize]
  apply (realizeL2Form_eq_iff_ae g μ _ _).mpr
  apply ae_of_all
  intro x
  change positiveIndicator (f x) • A x = if 0 < f x then A x else 0
  unfold positiveIndicator
  split_ifs <;> simp

end Yau.F04Proof
