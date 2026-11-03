import Yau.Proofs.F05BootstrapForcingContDiff
import Yau.Proofs.F05BootstrapNormalFields

/-! Finite contractions in the actual differentiated source preserve the
current joint order. The normal bootstrap supplies shorter Hessians to
these purely finite product and sum estimates. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_drift_contraction_contDiff {k : ℕ} {Q : Set (Point n)}
    {b : Point n → RIdx n → ℝ} {G : Point n → Space n →L[ℝ] ℝ}
    (hb : ∀ i, ContDiffOn ℝ k (fun z => b z i) Q) (hG : ContDiffOn ℝ k G Q) :
    ContDiffOn ℝ k (fun z => ∑ i,b z i*G z (realVec i)) Q := by
  apply ContDiffOn.sum
  intro i hi
  exact (hb i).mul (hG.clm_apply contDiffOn_const)

theorem F05_principal_contraction_contDiff {k : ℕ} {Q : Set (Point n)}
    {a : Point n → Mat n} {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (ha : ContDiffOn ℝ k a Q) (hH : ContDiffOn ℝ k H Q) :
    ContDiffOn ℝ k (fun z => ∑ i,∑ l,a z i l*H z (realVec i) (realVec l)) Q := by
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro l hl
  exact ((matrixEntryCLM i l).contDiff.comp_contDiffOn ha).mul
    ((hH.clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem F05_good_correction_contDiff {T : ℝ} {k : ℕ} {Q : Set (Point n)}
    (X : Set (Space n)) (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ)
    (s t : List (Option (RIdx n)))
    (ha : ContDiffOn ℝ k (F05GoodWord T s a) Q)
    (hb : ∀ i, ContDiffOn ℝ k (F05GoodWord T s (fun z => b z i)) Q)
    (hH : ContDiffOn ℝ k (F05RelDD X (F05GoodWord T t u)) Q)
    (hG : ContDiffOn ℝ k (F05RelD X (F05GoodWord T t u)) Q) :
    ContDiffOn ℝ k (F05GoodCorrection T X a b u s t) Q :=
  (F05_principal_contraction_contDiff ha hH).add (F05_drift_contraction_contDiff hb hG)

theorem F05_off_principal_contDiff {k : ℕ} {Q : Set (Point n)} (j : RIdx n)
    {a : Point n → Mat n} {H : Point n → Space n →L[ℝ] Space n →L[ℝ] ℝ}
    (ha : ContDiffOn ℝ k a Q)
    (hH : ∀ i l, i ≠ j ∨ l ≠ j → ContDiffOn ℝ k (fun z => H z (realVec i) (realVec l)) Q) :
    ContDiffOn ℝ k (fun z => ∑ i,∑ l,if i = j ∧ l = j then 0 else a z i l*H z (realVec i) (realVec l)) Q := by
  classical
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro l hl
  by_cases h : i = j ∧ l = j
  · simpa only [ite_eq_left h] using (contDiffOn_const : ContDiffOn ℝ k (fun _ : Point n => (0 : ℝ)) Q)
  · have hOff : i ≠ j ∨ l ≠ j := by tauto
    have hEntry : ContDiffOn ℝ k (fun z => a z i l) Q :=
      (matrixEntryCLM i l).contDiff.comp_contDiffOn ha
    have hProduct : ContDiffOn ℝ k (fun z => a z i l*H z (realVec i) (realVec l)) Q :=
      hEntry.mul (hH i l hOff)
    apply hProduct.congr
    intro z hz
    exact ite_eq_right h

end Yau.Proofs.F05Aux
