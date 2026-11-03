import Yau.Proofs.P06PositiveResidual

noncomputable section
open scoped ComplexOrder MatrixOrder ContinuousFunctionalCalculus

namespace Yau.NodeProofs.P06Aux.Clip

 theorem intervalResidual_positive_scalar {C : ℝ} (hC : 0 ≤ C) (r : ℝ) :
    max (r - intervalClip C r) 0 = max (r - C) 0 := by
  by_cases hu : C ≤ r
  · have hm : max (-C) r = r := max_eq_right (by linarith)
    simp only [intervalClip, hm, min_eq_left hu]
  · have hur : r ≤ C := (not_le.mp hu).le
    by_cases hl : r ≤ -C
    · have hm : max (-C) r = -C := max_eq_left hl
      have hn : min C (-C) = -C := min_eq_right (by linarith)
      simp only [intervalClip, hm, hn]
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    · have he : intervalClip C r = r := by
        rw [intervalClip, max_eq_right (not_le.mp hl).le, min_eq_right hur]
      rw [he, sub_self, max_self]
      exact (max_eq_right (sub_nonpos.mpr hur)).symm

theorem intervalResidual_negative_scalar {C : ℝ} (hC : 0 ≤ C) (r : ℝ) :
    max (intervalClip C r - r) 0 = max (-r - C) 0 := by
  by_cases hu : C ≤ r
  · have hm : max (-C) r = r := max_eq_right (by linarith)
    simp only [intervalClip, hm, min_eq_left hu]
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  · have hur : r ≤ C := (not_le.mp hu).le
    by_cases hl : r ≤ -C
    · have hm : max (-C) r = -C := max_eq_left hl
      have hn : min C (-C) = -C := min_eq_right (by linarith)
      simp only [intervalClip, hm, hn]
      congr 1
      ring
    · have he : intervalClip C r = r := by
        rw [intervalClip, max_eq_right (not_le.mp hl).le, min_eq_right hur]
      rw [he, sub_self, max_self]
      exact (max_eq_right (by linarith [not_le.mp hl])).symm

theorem matrixPositivePart_eq_cfc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixPositivePart A = cfc (fun r : ℝ => max r 0) A := by
  rw [matrixPositivePart, CFC.posPart_def, cfcₙ_eq_cfc]
  rfl

theorem matrixUpperResidual_eq_positive {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    matrixPositivePart (A - matrixIntervalClip C A) = matrixUpperResidual C A := by
  have hf := (intervalClip_lipschitz C).continuous
  have hg : Continuous (fun r : ℝ => r - intervalClip C r) := continuous_id.sub hf
  have hm : Continuous (fun r : ℝ => max r 0) := by fun_prop
  have he : A - matrixIntervalClip C A = cfc (fun r : ℝ => r - intervalClip C r) A := by
    rw [cfc_sub (a := A) (f := fun r : ℝ => r) (g := intervalClip C)
      continuous_id.continuousOn hf.continuousOn,
      cfc_id' ℝ A (show IsSelfAdjoint A from hA)]
    rfl
  rw [matrixPositivePart_eq_cfc, he, ← cfc_comp (fun r : ℝ => max r 0)
    (fun r : ℝ => r - intervalClip C r) A (show IsSelfAdjoint A from hA)
    hm.continuousOn hg.continuousOn]
  exact cfc_congr (fun r _ => intervalResidual_positive_scalar hC r)

theorem matrixLowerResidual_eq_positive {n : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    matrixPositivePart (matrixIntervalClip C A - A) = matrixLowerResidual C A := by
  have hf := (intervalClip_lipschitz C).continuous
  have hg : Continuous (fun r : ℝ => intervalClip C r - r) := hf.sub continuous_id
  have hm : Continuous (fun r : ℝ => max r 0) := by fun_prop
  have he : matrixIntervalClip C A - A = cfc (fun r : ℝ => intervalClip C r - r) A := by
    rw [cfc_sub (a := A) (f := intervalClip C) (g := fun r : ℝ => r)
      hf.continuousOn continuous_id.continuousOn,
      cfc_id' ℝ A (show IsSelfAdjoint A from hA)]
    rfl
  rw [matrixPositivePart_eq_cfc, he, ← cfc_comp (fun r : ℝ => max r 0)
    (fun r : ℝ => intervalClip C r - r) A (show IsSelfAdjoint A from hA)
    hm.continuousOn hg.continuousOn]
  exact cfc_congr (fun r _ => intervalResidual_negative_scalar hC r)

end Yau.NodeProofs.P06Aux.Clip
