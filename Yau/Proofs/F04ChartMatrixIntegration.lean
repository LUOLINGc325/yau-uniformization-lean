import Yau.Proofs.F04ChartSecondOrderIntegration
import Yau.Proofs.F04ChartWeakTestEntries

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.LeafProofs.L18Aux

/-- The whole actual matrix operator gives the exact finite sum of flux
 and coefficient-drift pairings. Every integral exchanged with a finite
 sum is integrable by the genuine compact test support. -/
theorem integral_chart_matrix_hessian
    {n : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    {a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun z => a z i j) O)
    {η v : ComplexVector n → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O)
    (hv : ContDiffOn ℝ 2 v O) :
    (∫ z in O, η z * ∑ i, ∑ j, a z i j * fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j)) =
      -(∫ z in O, ∑ i, ∑ j, rDeriv v z j * chartWeakTestEntry a η i j z) := by
  have hDv : ContDiffOn ℝ 1 (fderiv ℝ v) O := hv.fderiv_of_isOpen hO (by norm_num)
  have hDD : ContinuousOn (fderiv ℝ (fderiv ℝ v)) O :=
    hDv.continuousOn_fderiv_of_isOpen hO le_rfl
  have hDj (j : RIdx n) : ContinuousOn (fun z => rDeriv v z j) O :=
    hDv.continuousOn.clm_apply continuousOn_const
  have hLeft (i j : RIdx n) : IntegrableOn
      (fun z => η z * a z i j * fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j)) O volume := by
    have hDDij : ContinuousOn (fun z => fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j)) O :=
      (hDD.clm_apply continuousOn_const).clm_apply continuousOn_const
    have hh := integrable_compactTest_mul volume hO hη.continuous hcη hηO
      ((ha i j).continuousOn.mul hDDij)
    have hh' : Integrable (fun z => η z * a z i j *
        fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j)) volume := by
      simpa only [Pi.mul_apply, mul_assoc] using hh
    exact hh'.restrict
  have hRight (i j : RIdx n) : IntegrableOn
      (fun z => rDeriv v z j * chartWeakTestEntry a η i j z) O volume := by
    have hdη : Continuous (fun z => rDeriv η z i) :=
      (hη.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcdη : HasCompactSupport (fun z => rDeriv η z i) := hcη.fderiv_apply ℝ (realVec i)
    have hdηO : tsupport (fun z => rDeriv η z i) ⊆ O :=
      (tsupport_fderiv_apply_subset ℝ (realVec i)).trans hηO
    have hdA : ContinuousOn (fun z => rDeriv (fun w => a w i j) z i) O :=
      ((ha i j).continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
    have h₁ := integrable_compactTest_mul volume hO hdη hcdη hdηO
      ((ha i j).continuousOn.mul (hDj j))
    have h₂ := integrable_compactTest_mul volume hO hη.continuous hcη hηO (hdA.mul (hDj j))
    have he : (fun z => rDeriv v z j * chartWeakTestEntry a η i j z) =
        (fun z => rDeriv η z i * (a z i j * rDeriv v z j) +
          η z * (rDeriv (fun w => a w i j) z i * rDeriv v z j)) := by
      funext z
      unfold chartWeakTestEntry
      ring
    rw [he]
    exact (h₁.add h₂).restrict
  have hL : (∫ z in O, η z * ∑ i, ∑ j,
      a z i j * fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j)) =
      ∑ i, ∑ j, ∫ z in O, η z * a z i j * fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j) := by
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hLeft i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hLeft i j)
  have hR : (∫ z in O, ∑ i, ∑ j, rDeriv v z j * chartWeakTestEntry a η i j z) =
      ∑ i, ∑ j, ∫ z in O, rDeriv v z j * chartWeakTestEntry a η i j z := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hRight i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum Finset.univ (fun j _ => hRight i j)
  have hIP (i j : RIdx n) :
      (∫ z in O, η z * a z i j * fderiv ℝ (fderiv ℝ v) z (realVec i) (realVec j)) =
      -(∫ z in O, rDeriv v z j * chartWeakTestEntry a η i j z) :=
    integral_chart_coefficient_hessian hO hη hcη hηO (ha i j) hv i j
  rw [hL, hR]
  simp_rw [hIP]
  simp only [Finset.sum_neg_distrib]

end Yau.F04Proof
