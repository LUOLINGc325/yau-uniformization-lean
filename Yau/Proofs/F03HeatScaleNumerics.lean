import Yau.Proofs.F03MonotoneIntegral

/-! Elementary heat-scale interpolation, with one positive decay exponent. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
set_option maxHeartbeats 1200000

theorem min_one_le_rpow (x θ : ℝ) (hx : 0 ≤ x) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min 1 x ≤ x^θ := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    exact Real.self_le_rpow_of_le_one hx hx1 hθ1
  · have h1x : 1 ≤ x := (lt_of_not_ge hx1).le
    rw [min_eq_left h1x]
    exact Real.one_le_rpow h1x hθ

theorem heatScale_interpolation {p L t b : ℝ} (hp : 2 < p) (hL : 0 < L)
    (ht : 0 ≤ t) (hb : 0 < b) :
    min 1 (t*L^(p-1)*b^(-p/2)) ≤
      t^(1/(2*p))*L^(1/2-1/(2*p))*b^(-(1/4 : ℝ)) := by
  let β : ℝ := 1/(2*p)
  have hp0 : 0 < p := by linarith only [hp]
  have hβ0 : 0 < β := by dsimp [β];positivity
  have hβ1 : β ≤ 1 := by dsimp [β];apply (div_le_one (by positivity)).mpr;linarith only [hp]
  have hLpow : 0 ≤ L^(p-1) := Real.rpow_nonneg hL.le _
  have hbpow : 0 ≤ b^(-p/2) := Real.rpow_nonneg hb.le _
  have h := min_one_le_rpow (t*L^(p-1)*b^(-p/2)) β (mul_nonneg (mul_nonneg ht hLpow) hbpow) hβ0.le hβ1
  have heL : (p-1)*β=1/2-β := by dsimp [β];field_simp <;> ring
  have heb : (-p/2)*β=-(1/4 : ℝ) := by dsimp [β];field_simp <;> ring
  calc
    _ ≤ (t*L^(p-1)*b^(-p/2))^β := h
    _ = t^β*L^((p-1)*β)*b^((-p/2)*β) := by
      rw [Real.mul_rpow (mul_nonneg ht hLpow) hbpow,Real.mul_rpow ht hLpow,
        ← Real.rpow_mul hL.le,← Real.rpow_mul hb.le]
    _ = _ := by rw [heL,heb]

end Yau.Proofs.F03Aux
