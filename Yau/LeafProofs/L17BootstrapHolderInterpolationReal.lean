import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open scoped Topology
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapHolderInterpolationAux

def interpolationBudget (alpha beta S H : ℝ) : ℝ :=
  (2*S)^(1-beta/alpha)*H^(beta/alpha)

theorem interpolationBudget_nonneg {alpha beta S H : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H) :
    0 ≤ interpolationBudget alpha beta S H :=
  mul_nonneg (Real.rpow_nonneg (mul_nonneg (by norm_num) hS) _)
    (Real.rpow_nonneg hH _)

theorem le_geometric_of_le_both {v a b q : ℝ} (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hva : v ≤ a) (hvb : v ≤ b) :
    v ≤ a^(1-q)*b^q := by
  by_cases hv0 : v=0
  · rw [hv0]
    exact mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _)
  have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  calc
    v = v^(1-q)*v^q := by rw [← Real.rpow_add hvp]; simp
    _ ≤ a^(1-q)*b^q := mul_le_mul
      (Real.rpow_le_rpow hv hva (sub_nonneg.mpr hq1))
      (Real.rpow_le_rpow hv hvb hq) (Real.rpow_nonneg hv _) (Real.rpow_nonneg ha _)

theorem scalar_interpolation_quotient_bound {alpha beta S H d v : ℝ}
    (hba : 0 < beta ∧ beta < alpha) (hS : 0 ≤ S) (hH : 0 ≤ H) (hd : 0 < d)
    (hv : 0 ≤ v) (hSup : v ≤ 2*S) (hPair : v ≤ H*d^alpha) :
    v/d^beta ≤ interpolationBudget alpha beta S H := by
  have ha : 0 < alpha := hba.1.trans hba.2
  have hq : 0 ≤ beta/alpha := (div_pos hba.1 ha).le
  have hq1 : beta/alpha ≤ 1 := (div_le_one ha).mpr hba.2.le
  have hGeom := le_geometric_of_le_both hv (mul_nonneg (by norm_num) hS)
    (mul_nonneg hH (Real.rpow_nonneg hd.le _)) hq hq1 hSup hPair
  have hPow : (H*d^alpha)^(beta/alpha)=H^(beta/alpha)*d^beta := by
    rw [Real.mul_rpow hH (Real.rpow_nonneg hd.le _),← Real.rpow_mul hd.le]
    have he : alpha*(beta/alpha)=beta := by field_simp [ha.ne']
    rw [he]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hd beta)).mpr
  calc
    v ≤ (2*S)^(1-beta/alpha)*(H*d^alpha)^(beta/alpha) := hGeom
    _ = interpolationBudget alpha beta S H*d^beta := by rw [hPow]; dsimp only [interpolationBudget]; ring

theorem holder_interpolation_pair_bound {X F : Type*} [NormedAddCommGroup F]
    {f : X → F} {d : X → X → ℝ} {alpha beta S H : ℝ}
    (hba : 0 < beta ∧ beta < alpha) (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hSup : ∀ x, ‖f x‖ ≤ S)
    (hPair : ∀ x y, ‖f x-f y‖ ≤ H*(d x y)^alpha) :
    ∀ x y, 0 < d x y → ‖f x-f y‖/(d x y)^beta ≤
      (2*S)^(1-beta/alpha)*H^(beta/alpha) := by
  intro x y hd
  apply scalar_interpolation_quotient_bound hba hS hH hd (norm_nonneg _) _ (hPair x y)
  exact (norm_sub_le _ _).trans (by linarith [hSup x,hSup y])

theorem half_quarter_budget_le {A eps : ℝ} (hA : 0 ≤ A) (heps : 0 ≤ eps) (heps1 : eps ≤ 1) :
    max (A*eps^(1/2 : ℝ))
      (interpolationBudget (1/2) (1/4) (A*eps^(1/2 : ℝ)) (2*A)) ≤
      4*A*eps^(1/4 : ℝ) := by
  have h2sq : ((2 : ℝ)^(1/2 : ℝ))^2=2 := by
    rw [sq,← Real.rpow_add (by norm_num : (0 : ℝ)<2)]
    norm_num
  have hAsq : (A^(1/2 : ℝ))^2=A := by
    rw [sq,← Real.rpow_add' hA (by norm_num : (1/2 : ℝ)+(1/2)≠0)]
    norm_num
  have hePow : (eps^(1/2 : ℝ))^(1/2 : ℝ)=eps^(1/4 : ℝ) := by
    rw [← Real.rpow_mul heps]
    norm_num
  have hBudget : interpolationBudget (1/2) (1/4) (A*eps^(1/2 : ℝ)) (2*A)=
      2*A*eps^(1/4 : ℝ) := by
    dsimp only [interpolationBudget]
    norm_num only [show (1/4 : ℝ)/(1/2)=1/2 by norm_num,show (1 : ℝ)-1/2=1/2 by norm_num]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2) (mul_nonneg hA (Real.rpow_nonneg heps _)),
      Real.mul_rpow hA (Real.rpow_nonneg heps _),hePow,
      Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hA]
    calc
      _ = ((2 : ℝ)^(1/2 : ℝ))^2*(A^(1/2 : ℝ))^2*eps^(1/4 : ℝ) := by ring
      _ = _ := by rw [h2sq,hAsq]
  have hPower : eps^(1/2 : ℝ) ≤ eps^(1/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' heps heps1 (by norm_num) (by norm_num)
  have hN : 0 ≤ A*eps^(1/4 : ℝ) := mul_nonneg hA (Real.rpow_nonneg heps _)
  rw [hBudget]
  apply max_le
  · have h := mul_le_mul_of_nonneg_left hPower hA
    linarith
  · nlinarith

end Yau.LeafProofs.L17BootstrapHolderInterpolationAux
