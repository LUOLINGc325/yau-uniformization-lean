import Yau.LeafProofs.L17ParabolicOperatorCoefficients
import Yau.LeafProofs.L17FrozenPhysicalHeat

open Set Metric
open scoped Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17ParabolicOperatorAux

theorem spatialLipschitz_holderBound_ball {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {R T γ A L : ℝ} (hR : 0 < R) (hγ : γ ≤ 1) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (f : Space n → V) (hSup : ∀ z ∈ ball (0 : Space n) R, ‖f z‖ ≤ A)
    (hLip : ∀ z ∈ ball (0 : Space n) R, ∀ w ∈ ball (0 : Space n) R,
      ‖f z - f w‖ ≤ L * ‖z - w‖) :
    HolderBound γ (cylinder (ball (0 : Space n) R) 0 T) (fun q => f q.1)
      (A + L * (2 * R) ^ (1 - γ)) := by
  have hC : 0 ≤ A + L * (2 * R) ^ (1 - γ) := by positivity
  have hLC : L * (2 * R) ^ (1 - γ) ≤ A + L * (2 * R) ^ (1 - γ) := le_add_of_nonneg_left hA
  refine ⟨hC, fun q hq => (hSup q.1 hq.1).trans (le_add_of_nonneg_right (by positivity)), ?_⟩
  intro q hq r hr
  have hd0 : 0 ≤ ‖q.1-r.1‖ := norm_nonneg _
  have hdR : ‖q.1-r.1‖ ≤ 2 * R := by
    have hqR : ‖q.1‖ < R := by simpa only [mem_ball,dist_zero_right] using hq.1
    have hrR : ‖r.1‖ < R := by simpa only [mem_ball,dist_zero_right] using hr.1
    exact (norm_sub_le _ _).trans (by linarith)
  have hdPow : ‖q.1-r.1‖ ≤ (2*R)^(1-γ) * ‖q.1-r.1‖^γ := by
    by_cases hd : ‖q.1-r.1‖ = 0
    · rw [hd]
      positivity
    · have hdpos : 0 < ‖q.1-r.1‖ := lt_of_le_of_ne hd0 (Ne.symm hd)
      calc
        _ = ‖q.1-r.1‖^(1-γ) * ‖q.1-r.1‖^γ := by rw [← Real.rpow_add hdpos]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hd0 hdR (sub_nonneg.mpr hγ)) (Real.rpow_nonneg hd0 _)
  calc
    _ ≤ L * ‖q.1-r.1‖ := hLip q.1 hq.1 r.1 hr.1
    _ ≤ L * ((2*R)^(1-γ)*‖q.1-r.1‖^γ) := mul_le_mul_of_nonneg_left hdPow hL
    _ = (L*(2*R)^(1-γ))*‖q.1-r.1‖^γ := by ring
    _ ≤ (A+L*(2*R)^(1-γ))*‖q.1-r.1‖^γ :=
      mul_le_mul_of_nonneg_right hLC (Real.rpow_nonneg hd0 _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) hC

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem scaled_chartCoefficient_holderBound (A : BoundedChartFamily g)
    {ρ T γ : ℝ} (hρ : 0 < ρ) (hRadius : 2 * ρ < A.radius) (hγ : γ ≤ 1) (p : M.Carrier) :
    HolderBound γ (cylinder (ball (0 : Space n) 2) 0 T)
      (fun q => chartCoefficient A p (ρ • q.1))
      (coefficientBudget A + coefficientBudget A * ρ * (4 : ℝ) ^ (1-γ)) := by
  have hB : 0 ≤ coefficientBudget A := zero_le_one.trans (coefficientBudget_ge_one A)
  have hMap : ∀ z ∈ ball (0 : Space n) 2, ρ • z ∈ ball (0 : Space n) A.radius := by
    intro z hz
    have hzNorm : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hρ] using
      (mul_lt_mul_of_pos_left hzNorm hρ).trans (by linarith [hRadius])
  have h := spatialLipschitz_holderBound_ball (T := T) (by norm_num : (0 : ℝ) < 2) hγ hB
    (mul_nonneg hB hρ.le) (fun z => chartCoefficient A p (ρ • z))
    (fun z hz => (chartCoefficient_bounds A p (hMap z hz)).1) ?_
  · simpa only [show (2 : ℝ)*2=4 by norm_num] using h
  · intro z hz w hw
    have hh := chartCoefficient_lipschitz A p (hMap z hz) (hMap w hw)
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hρ] at hh
    exact hh.trans_eq (by ring)

theorem scaled_frozenCoefficient_holderBound (A : BoundedChartFamily g)
    {ρ T γ : ℝ} (hρ : 0 < ρ) (hRadius : 2 * ρ < A.radius) (hγ : γ ≤ 1) (p : M.Carrier) :
    HolderBound γ (cylinder (ball (0 : Space n) 2) 0 T)
      (fun q => chartCoefficient A p 0 - chartCoefficient A p (ρ • q.1))
      (2 * coefficientBudget A * ρ + coefficientBudget A * ρ * (4 : ℝ) ^ (1-γ)) := by
  have hB : 0 ≤ coefficientBudget A := zero_le_one.trans (coefficientBudget_ge_one A)
  have hMap : ∀ z ∈ ball (0 : Space n) 2, ρ • z ∈ ball (0 : Space n) A.radius := by
    intro z hz
    have hzNorm : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hρ] using
      (mul_lt_mul_of_pos_left hzNorm hρ).trans (by linarith [hRadius])
  have hZero : (0 : Space n) ∈ ball 0 A.radius := mem_ball_self A.radius_pos
  have h := spatialLipschitz_holderBound_ball (T := T) (by norm_num : (0 : ℝ) < 2) hγ
    (by positivity : 0 ≤ 2 * coefficientBudget A * ρ) (mul_nonneg hB hρ.le)
    (fun z => chartCoefficient A p 0 - chartCoefficient A p (ρ • z)) ?_ ?_
  · simpa only [show (2 : ℝ)*2=4 by norm_num] using h
  · intro z hz
    have hzNorm : ‖z‖ ≤ 2 := le_of_lt (by simpa only [mem_ball,dist_zero_right] using hz)
    have hh := chartCoefficient_lipschitz A p hZero (hMap z hz)
    rw [zero_sub,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hρ] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzNorm hρ.le) hB)).trans_eq (by ring)
  · intro z hz w hw
    have heq : (chartCoefficient A p 0 - chartCoefficient A p (ρ • z)) -
        (chartCoefficient A p 0 - chartCoefficient A p (ρ • w)) =
        chartCoefficient A p (ρ • w) - chartCoefficient A p (ρ • z) := by abel
    rw [heq]
    have hh := chartCoefficient_lipschitz A p (hMap w hw) (hMap z hz)
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hρ,norm_sub_rev w z] at hh
    exact hh.trans_eq (by ring)

theorem holderBound_matrix_entry_max {γ C : ℝ} {Q : Set (Point n)}
    {a : Point n → Mat n} (ha : HolderBound γ Q a C) (i j : RIdx n) :
    HolderBound γ Q (fun q => a q i j) C := by
  refine ⟨ha.1,?_,?_⟩
  · intro q hq
    exact ((norm_le_pi_norm (a q i) j).trans (norm_le_pi_norm (a q) i)).trans (ha.2.1 q hq)
  · intro q hq r hr
    exact ((norm_le_pi_norm ((a q-a r) i) j).trans (norm_le_pi_norm (a q-a r) i)).trans
      (ha.2.2 q hq r hr)

end Yau.LeafProofs.L17Aux
