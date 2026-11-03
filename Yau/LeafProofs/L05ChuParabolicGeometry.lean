import Yau.LeafProofs.L05ChuCutoffModulus
import Mathlib.Analysis.MeanInequalitiesPow

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem chu_parabolicDistance_triangle {n : ℕ} (p q z : Point n) :
    parabolicDistance p q ≤ parabolicDistance p z+parabolicDistance z q := by
  have hx := norm_sub_le_norm_sub_add_norm_sub p.1 z.1 q.1
  have ht := abs_sub_le p.2 z.2 q.2
  have htime : Real.sqrt |p.2-q.2| ≤ Real.sqrt |p.2-z.2|+Real.sqrt |z.2-q.2| := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),?_⟩
    nlinarith only [ht,Real.sq_sqrt (abs_nonneg (p.2-z.2)),Real.sq_sqrt (abs_nonneg (z.2-q.2)),
      mul_nonneg (Real.sqrt_nonneg |p.2-z.2|) (Real.sqrt_nonneg |z.2-q.2|)]
  unfold parabolicDistance
  linarith only [hx,htime]

theorem chu_parabolicDistance_rpow_le_weight {n : ℕ} {gamma : ℝ}
    (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1) (p q : Point n) :
    (parabolicDistance p q)^gamma ≤ holderWeight gamma p q := by
  unfold parabolicDistance holderWeight
  calc
    _ ≤ ‖p.1-q.1‖^gamma+(Real.sqrt |p.2-q.2|)^gamma :=
      Real.rpow_add_le_add_rpow (norm_nonneg _) (Real.sqrt_nonneg _) hg hg1
    _ = _ := by rw [← Real.rpow_div_two_eq_sqrt gamma (abs_nonneg _)]

theorem chu_holderBound_of_near_power {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {J : Point n → V} {gamma rho M C : ℝ}
    (hg : 0 ≤ gamma) (hg1 : gamma ≤ 1) (hrho : 0 < rho) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hSup : ∀ p ∈ Q, ‖J p‖ ≤ M)
    (hNear : ∀ p ∈ Q, ∀ q ∈ Q, parabolicDistance p q ≤ rho →
      ‖J p-J q‖ ≤ C*(parabolicDistance p q)^gamma) :
    HolderBound gamma Q J (M+C+2*M*rho^(-gamma)) := by
  have hFarC : 0 ≤ 2*M*rho^(-gamma) := by positivity
  have hTot : 0 ≤ M+C+2*M*rho^(-gamma) := by positivity
  refine ⟨hTot,?_,?_⟩
  · intro p hp
    exact (hSup p hp).trans (by linarith only [hC,hFarC])
  · intro p hp q hq
    have hW : 0 ≤ holderWeight gamma p q :=
      add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)
    have hPow := chu_parabolicDistance_rpow_le_weight hg hg1 p q
    by_cases hpqNear : parabolicDistance p q ≤ rho
    · exact ((hNear p hp q hq hpqNear).trans (mul_le_mul_of_nonneg_left hPow hC)).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hM,hFarC]) hW)
    · have hF := Real.rpow_le_rpow hrho.le (le_of_not_ge hpqNear) hg
      have hOne : 1 ≤ rho^(-gamma)*holderWeight gamma p q := by
        calc
          1=rho^(-gamma)*rho^gamma := by rw [← Real.rpow_add hrho,neg_add_cancel,Real.rpow_zero]
          _≤rho^(-gamma)*(parabolicDistance p q)^gamma :=
            mul_le_mul_of_nonneg_left hF (Real.rpow_nonneg hrho.le _)
          _≤_ := mul_le_mul_of_nonneg_left hPow (Real.rpow_nonneg hrho.le _)
      have hDiff : ‖J p-J q‖ ≤ 2*M := by
        exact (norm_sub_le _ _).trans ((add_le_add (hSup p hp) (hSup q hq)).trans_eq (by ring))
      have hScale := mul_le_mul_of_nonneg_left hOne (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hM)
      have hCoeff := mul_le_mul_of_nonneg_right (show 2*M*rho^(-gamma) ≤ M+C+2*M*rho^(-gamma) by linarith only [hM,hC]) hW
      nlinarith only [hDiff,hScale,hCoeff]

end Yau.LeafProofs.L05Aux
