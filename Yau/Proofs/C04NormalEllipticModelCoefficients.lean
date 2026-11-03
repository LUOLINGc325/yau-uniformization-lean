import Yau.Proofs.C04NormalEllipticModelEllipticity

/-! Fixed continuous evaluations for the exact principal and drift coefficient
formulas. Their norms depend only on the fixed Euclidean model. -/

noncomputable section

namespace Yau.Proofs.C04Aux
open Yau Yau.LeafProofs.L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {n : ℕ}

def normalEllipticCoordEval (c i : RIdx n) :
    (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] ℝ :=
  (realCoordCLM i).comp (ContinuousLinearMap.apply ℝ (ComplexVector n) (realVec c))

@[simp] theorem normalEllipticCoordEval_apply (c i : RIdx n)
    (B : ComplexVector n →L[ℝ] ComplexVector n) :
    normalEllipticCoordEval c i B = realCoord (B (realVec c)) i := realCoordCLM_apply _ _

def normalEllipticPrincipalBilinear (i j : RIdx n) :
    (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ]
      (ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ c : RIdx n, (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (normalEllipticCoordEval c i) (normalEllipticCoordEval c j)

theorem normalEllipticPrincipal_as_bilinear
    (B : ComplexVector n →L[ℝ] ComplexVector n) (i j : RIdx n) :
    normalEllipticPrincipal B i j = normalEllipticPrincipalBilinear i j B B := by
  simp [normalEllipticPrincipalBilinear, normalEllipticPrincipal]

def normalEllipticGammaEval (i j k : RIdx n) :
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) →L[ℝ] ℝ :=
  (realCoordCLM k).comp
    ((ContinuousLinearMap.apply ℝ (ComplexVector n) (realVec j)).comp
      (ContinuousLinearMap.apply ℝ (ComplexVector n →L[ℝ] ComplexVector n) (realVec i)))

@[simp] theorem normalEllipticGammaEval_apply (i j k : RIdx n)
    (G : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) :
    normalEllipticGammaEval i j k G = realCoord (G (realVec i) (realVec j)) k :=
  realCoordCLM_apply _ _

def normalEllipticDrift (B : ComplexVector n →L[ℝ] ComplexVector n)
    (G : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) (k : RIdx n) : ℝ :=
  -∑ i : RIdx n, ∑ j : RIdx n,
    normalEllipticPrincipal B i j * realCoord (G (realVec i) (realVec j)) k

def normalEllipticPrincipalNormConstant (n : ℕ) : ℝ :=
  1 + ∑ p : RIdx n × RIdx n, ‖normalEllipticPrincipalBilinear p.1 p.2‖

def normalEllipticGammaNormConstant (n : ℕ) : ℝ :=
  1 + ∑ p : RIdx n × RIdx n × RIdx n, ‖normalEllipticGammaEval p.1 p.2.1 p.2.2‖

theorem normalEllipticPrincipalNormConstant_pos (n : ℕ) :
    0 < normalEllipticPrincipalNormConstant n := by
  have hh : 0 ≤ ∑ p : RIdx n × RIdx n, ‖normalEllipticPrincipalBilinear p.1 p.2‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  dsimp [normalEllipticPrincipalNormConstant]
  linarith

theorem normalEllipticGammaNormConstant_pos (n : ℕ) :
    0 < normalEllipticGammaNormConstant n := by
  have hh : 0 ≤ ∑ p : RIdx n × RIdx n × RIdx n,
      ‖normalEllipticGammaEval p.1 p.2.1 p.2.2‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  dsimp [normalEllipticGammaNormConstant]
  linarith

theorem normal_elliptic_nonneg_value_le_one_sum {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (i : ι) : f i ≤ 1 + ∑ j, f j := by
  have hh : f i ≤ ∑ j, f j := Finset.single_le_sum (fun j hj => hf j) (Finset.mem_univ i)
  linarith

theorem normalEllipticPrincipalBilinear_norm (i j : RIdx n) :
    ‖normalEllipticPrincipalBilinear i j‖ ≤ normalEllipticPrincipalNormConstant n := by
  exact normal_elliptic_nonneg_value_le_one_sum
    (fun p : RIdx n × RIdx n => ‖normalEllipticPrincipalBilinear p.1 p.2‖)
    (fun p => norm_nonneg (normalEllipticPrincipalBilinear p.1 p.2)) (i, j)

theorem normalEllipticGammaEval_norm (i j k : RIdx n) :
    ‖normalEllipticGammaEval i j k‖ ≤ normalEllipticGammaNormConstant n := by
  exact normal_elliptic_nonneg_value_le_one_sum
    (fun p : RIdx n × RIdx n × RIdx n => ‖normalEllipticGammaEval p.1 p.2.1 p.2.2‖)
    (fun p => norm_nonneg (normalEllipticGammaEval p.1 p.2.1 p.2.2)) (i, j, k)

end Yau.Proofs.C04Aux
