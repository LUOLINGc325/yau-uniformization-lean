import Yau.LeafProofs.L17LocalizedSchauderUnitSource

open Set Metric
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17HolderAux

variable {n : ℕ}

theorem unitParabolicDistance_nonneg {ρ : ℝ} (hρ : 0 < ρ) {T : ℝ}
    (q r : ComplexVector n × Time T) : 0 ≤ unitParabolicDistance ρ q r :=
  add_nonneg (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hρ.le)

theorem unitParabolicDistance_space_le {ρ : ℝ} (hρ : 0 < ρ) {T : ℝ}
    (q r : ComplexVector n × Time T) : ‖q.1-r.1‖ ≤ unitParabolicDistance ρ q r :=
  le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hρ.le)

theorem unitParabolicDistance_symm (ρ : ℝ) {T : ℝ} (q r : ComplexVector n × Time T) :
    unitParabolicDistance ρ q r = unitParabolicDistance ρ r q := by
  unfold unitParabolicDistance
  rw [norm_sub_rev q.1 r.1,abs_sub_comm (q.2 : ℝ) (r.2 : ℝ)]

theorem self_le_rpow_on_unit {d gamma : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) : d ≤ d^gamma := by
  by_cases hz : d = 0
  · rw [hz,Real.zero_rpow hgamma.ne']
  · have hp : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    calc
      d = d^(1 : ℝ) := (Real.rpow_one d).symm
      _ ≤ d^gamma := Real.rpow_le_rpow_of_exponent_ge hp hd1 hgamma1

theorem unitParabolicDistance_map_le {ρ L : ℝ} (hρ : 0 < ρ) (hL : 1 ≤ L) {T : ℝ}
    (τ : ComplexVector n → ComplexVector n) (q r : ComplexVector n × Time T)
    (hLip : ‖τ q.1-τ r.1‖ ≤ L*‖q.1-r.1‖) :
    unitParabolicDistance ρ (τ q.1,q.2) (τ r.1,r.2) ≤ L*unitParabolicDistance ρ q r := by
  have hTime : 0 ≤ Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)|/ρ := div_nonneg (Real.sqrt_nonneg _) hρ.le
  dsimp only [unitParabolicDistance]
  calc
    _ ≤ L*‖q.1-r.1‖+Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)|/ρ := add_le_add hLip (le_refl _)
    _ ≤ L*‖q.1-r.1‖+L*(Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)|/ρ) :=
      add_le_add (le_refl _) (le_mul_of_one_le_left hTime hL)
    _ = _ := by ring

theorem unitParabolicDistance_map_rpow_le {ρ L gamma : ℝ} (hρ : 0 < ρ) (hL : 1 ≤ L)
    (hgamma : 0 ≤ gamma) {T : ℝ} (τ : ComplexVector n → ComplexVector n)
    (q r : ComplexVector n × Time T) (hLip : ‖τ q.1-τ r.1‖ ≤ L*‖q.1-r.1‖) :
    (unitParabolicDistance ρ (τ q.1,q.2) (τ r.1,r.2))^gamma ≤
      L^gamma*(unitParabolicDistance ρ q r)^gamma := by
  calc
    _ ≤ (L*unitParabolicDistance ρ q r)^gamma := Real.rpow_le_rpow
      (unitParabolicDistance_nonneg hρ _ _) (unitParabolicDistance_map_le hρ hL τ q r hLip) hgamma
    _ = _ := Real.mul_rpow (zero_le_one.trans hL) (unitParabolicDistance_nonneg hρ q r)

end Yau.LeafProofs.L17LocalizedSchauderAux
