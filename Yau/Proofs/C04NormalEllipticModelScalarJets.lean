import Yau.Proofs.C04NormalEllipticModelCoefficients
import Yau.Proofs.C04NormalEllipticModelCalculus

/-! Uniform scalar coefficient jets from operator and connection jets.
Only fixed continuous evaluations and finite sums occur. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {n : ℕ} {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

def normalEllipticPrincipalJetBudget (n : ℕ) (P : ℕ → ℝ) (m : ℕ) : ℝ :=
  normalEllipticPrincipalNormConstant n * ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * P i * P (m - i)

theorem normalEllipticPrincipalJetBudget_nonneg (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (m : ℕ) :
    0 ≤ normalEllipticPrincipalJetBudget n P m :=
  mul_nonneg (normalEllipticPrincipalNormConstant_pos n).le
    (Finset.sum_nonneg fun i hi => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hP i)) (hP _))

theorem normal_elliptic_principal_smooth
    (B : D → ComplexVector n →L[ℝ] ComplexVector n) {U : Set D}
    (hB : ContDiffOn ℝ ∞ B U) (i j : RIdx n) :
    ContDiffOn ℝ ∞ (fun x => normalEllipticPrincipal (B x) i j) U := by
  have he : (fun x => normalEllipticPrincipal (B x) i j) =
      fun x => normalEllipticPrincipalBilinear i j (B x) (B x) := by
    funext x
    exact normalEllipticPrincipal_as_bilinear _ _ _
  rw [he]
  exact ((normalEllipticPrincipalBilinear i j).contDiff.comp_contDiffOn hB).clm_apply hB

theorem normal_elliptic_principal_jet
    (B : D → ComplexVector n →L[ℝ] ComplexVector n) {U : Set D}
    (hB : ContDiffOn ℝ ∞ B U) (hU : IsOpen U) {x : D} (hx : x ∈ U)
    (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j)
    (hjet : ∀ j, ‖iteratedFDeriv ℝ j B x‖ ≤ P j) (m : ℕ) (i j : RIdx n) :
    ‖iteratedFDeriv ℝ m (fun y => normalEllipticPrincipal (B y) i j) x‖ ≤
      normalEllipticPrincipalJetBudget n P m := by
  have he : (fun y => normalEllipticPrincipal (B y) i j) =
      fun y => normalEllipticPrincipalBilinear i j (B y) (B y) := by
    funext y
    exact normalEllipticPrincipal_as_bilinear _ _ _
  rw [he]
  have hh := normal_elliptic_bilinear_jet (normalEllipticPrincipalBilinear i j)
    hB hB hU hx P P hP hjet hjet m
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (normalEllipticPrincipalBilinear_norm i j)
    (Finset.sum_nonneg fun i hi => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hP i)) (hP _))

theorem normal_elliptic_gamma_eval_smooth
    (G : D → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) {U : Set D}
    (hG : ContDiffOn ℝ ∞ G U) (i j k : RIdx n) :
    ContDiffOn ℝ ∞ (fun x => realCoord (G x (realVec i) (realVec j)) k) U := by
  have he : (fun x => realCoord (G x (realVec i) (realVec j)) k) =
      fun x => normalEllipticGammaEval i j k (G x) := by
    funext x
    exact (normalEllipticGammaEval_apply _ _ _ _).symm
  rw [he]
  exact (normalEllipticGammaEval i j k).contDiff.comp_contDiffOn hG

theorem normal_elliptic_gamma_eval_jet
    (G : D → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) {U : Set D}
    (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U) {x : D} (hx : x ∈ U)
    (Q : ℕ → ℝ) (hQ : ∀ j, 0 ≤ Q j)
    (hjet : ∀ j, ‖iteratedFDeriv ℝ j G x‖ ≤ Q j) (m : ℕ) (i j k : RIdx n) :
    ‖iteratedFDeriv ℝ m (fun y => realCoord (G y (realVec i) (realVec j)) k) x‖ ≤
      normalEllipticGammaNormConstant n * Q m := by
  have he : (fun y => realCoord (G y (realVec i) (realVec j)) k) =
      fun y => normalEllipticGammaEval i j k (G y) := by
    funext y
    exact (normalEllipticGammaEval_apply _ _ _ _).symm
  rw [he]
  exact (normal_elliptic_linear_jet (normalEllipticGammaEval i j k) hG hU hx m).trans
    (mul_le_mul (normalEllipticGammaEval_norm i j k) (hjet m) (norm_nonneg _)
      (normalEllipticGammaNormConstant_pos n).le)

def normalEllipticDriftJetBudget (n : ℕ) (P Q : ℕ → ℝ) (m : ℕ) : ℝ :=
  (Fintype.card (RIdx n) : ℝ) ^ 2 * ‖ContinuousLinearMap.mul ℝ ℝ‖ *
    ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * normalEllipticPrincipalJetBudget n P i *
      (normalEllipticGammaNormConstant n * Q (m - i))

theorem normalEllipticDriftJetBudget_nonneg (P Q : ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hQ : ∀ j, 0 ≤ Q j) (m : ℕ) :
    0 ≤ normalEllipticDriftJetBudget n P Q m := by
  unfold normalEllipticDriftJetBudget
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))
    (Finset.sum_nonneg fun i hi => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (normalEllipticPrincipalJetBudget_nonneg P hP i))
      (mul_nonneg (normalEllipticGammaNormConstant_pos n).le (hQ _)))

theorem normal_elliptic_drift_smooth
    (B : D → ComplexVector n →L[ℝ] ComplexVector n)
    (G : D → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) {U : Set D}
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (k : RIdx n) :
    ContDiffOn ℝ ∞ (fun x => normalEllipticDrift (B x) (G x) k) U := by
  exact (ContDiffOn.sum fun i hi => ContDiffOn.sum fun j hj =>
    (normal_elliptic_principal_smooth B hB i j).mul
      (normal_elliptic_gamma_eval_smooth G hG i j k)).neg

theorem normal_elliptic_drift_jet
    (B : D → ComplexVector n →L[ℝ] ComplexVector n)
    (G : D → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) {U : Set D}
    (hB : ContDiffOn ℝ ∞ B U) (hG : ContDiffOn ℝ ∞ G U) (hU : IsOpen U)
    {x : D} (hx : x ∈ U) (P Q : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (hQ : ∀ j, 0 ≤ Q j)
    (hbjet : ∀ j, ‖iteratedFDeriv ℝ j B x‖ ≤ P j)
    (hgjet : ∀ j, ‖iteratedFDeriv ℝ j G x‖ ≤ Q j) (m : ℕ) (k : RIdx n) :
    ‖iteratedFDeriv ℝ m (fun y => normalEllipticDrift (B y) (G y) k) x‖ ≤
      normalEllipticDriftJetBudget n P Q m := by
  let N : ℝ := Fintype.card (RIdx n)
  let T : ℝ := ‖ContinuousLinearMap.mul ℝ ℝ‖ *
    ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * normalEllipticPrincipalJetBudget n P i *
      (normalEllipticGammaNormConstant n * Q (m - i))
  let f : RIdx n → RIdx n → D → ℝ := fun i j y =>
    normalEllipticPrincipal (B y) i j * realCoord (G y (realVec i) (realVec j)) k
  have hf (i j : RIdx n) : ContDiffOn ℝ ∞ (f i j) U :=
    (normal_elliptic_principal_smooth B hB i j).mul
      (normal_elliptic_gamma_eval_smooth G hG i j k)
  have hfb (i j : RIdx n) : ‖iteratedFDeriv ℝ m (f i j) x‖ ≤ T :=
    normal_elliptic_bilinear_jet (ContinuousLinearMap.mul ℝ ℝ)
      (normal_elliptic_principal_smooth B hB i j) (normal_elliptic_gamma_eval_smooth G hG i j k)
      hU hx (normalEllipticPrincipalJetBudget n P) (fun r => normalEllipticGammaNormConstant n * Q r)
      (normalEllipticPrincipalJetBudget_nonneg P hP)
      (fun r => normal_elliptic_principal_jet B hB hU hx P hP hbjet r i j)
      (fun r => normal_elliptic_gamma_eval_jet G hG hU hx Q hQ hgjet r i j k) m
  have hinner (i : RIdx n) : ‖iteratedFDeriv ℝ m (fun y => ∑ j : RIdx n, f i j y) x‖ ≤ N * T := by
    have hh := normal_elliptic_sum_jet Finset.univ (f i) (fun j hj => hf i j) hU hx m
      (fun _ => T) (fun j hj => hfb i j)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  have hsmooth : ContDiffOn ℝ ∞ (fun y => ∑ i : RIdx n, ∑ j : RIdx n, f i j y) U :=
    ContDiffOn.sum fun i hi => ContDiffOn.sum fun j hj => hf i j
  have hsum : ‖iteratedFDeriv ℝ m (fun y => ∑ i : RIdx n, ∑ j : RIdx n, f i j y) x‖ ≤
      N * (N * T) := by
    have hh := normal_elliptic_sum_jet Finset.univ (fun i y => ∑ j : RIdx n, f i j y)
      (fun i hi => ContDiffOn.sum fun j hj => hf i j) hU hx m (fun _ => N * T)
      (fun i hi => hinner i)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  have hneg : ‖-(ContinuousLinearMap.id ℝ ℝ)‖ ≤ 1 := by
    simpa only [norm_neg] using (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := ℝ))
  have hh := normal_elliptic_linear_jet (-(ContinuousLinearMap.id ℝ ℝ)) hsmooth hU hx m
  apply (hh.trans (mul_le_of_le_one_left (norm_nonneg _) hneg)).trans
  exact hsum.trans_eq (by dsimp [normalEllipticDriftJetBudget, N, T]; ring)

end Yau.Proofs.C04Aux
