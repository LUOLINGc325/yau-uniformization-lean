import Yau.Proofs.F03HeatInterpolation

/-! Actual scale factors and zero-endpoint integrals for the heat correction and its gradient. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace Yau.Proofs.F03Aux

theorem heat_interpolation_scale {t L b θ : ℝ} (ht : 0 < t) (hL : 0 < L) (hb : 0 < b) :
    (t/L)^θ*(L/Real.sqrt b)^((1 : ℝ)/2)=
      t^θ*L^((1 : ℝ)/2-θ)*b^(-(1 : ℝ)/4) := by
  rw [Real.div_rpow ht.le hL.le,Real.div_rpow hL.le (Real.sqrt_nonneg b),
    Real.sqrt_eq_rpow,← Real.rpow_mul hb.le,Real.rpow_sub hL]
  norm_num
  rw [Real.rpow_neg hb.le]
  ring

theorem heat_minimum_quarter_bound {p t L b : ℝ}
    (hp : 2 < p) (ht : 0 < t) (hL : 0 < L) (hb : 0 < b) :
    min 1 ((t/L)*(L/Real.sqrt b)^p) ≤
      t^((1 : ℝ)/(2*p))*L^((1 : ℝ)/2-(1 : ℝ)/(2*p))*b^(-(1 : ℝ)/4) := by
  have hScale : (t/L)*(L/Real.sqrt b)^p=t*L^(p-1)*b^(-p/2) := by
    rw [Real.div_rpow hL.le (Real.sqrt_nonneg b),Real.sqrt_eq_rpow,
      ← Real.rpow_mul hb.le,Real.rpow_sub hL,Real.rpow_one]
    rw [show (1 : ℝ)/2*p=p/2 by ring,show -p/2=-(p/2) by ring,Real.rpow_neg hb.le]
    ring
  rw [hScale]
  simpa only [neg_div] using heatScale_interpolation hp hL ht.le hb

theorem heat_gradient_three_quarter_bound {p t L b : ℝ}
    (hp : 2 < p) (ht : 0 < t) (hL : 0 < L) (hb : 0 < b) :
    (1/Real.sqrt b)*min 1 ((t/L)*(L/Real.sqrt b)^p) ≤
      t^((1 : ℝ)/(2*p))*L^((1 : ℝ)/2-(1 : ℝ)/(2*p))*b^(-(3 : ℝ)/4) := by
  have h := mul_le_mul_of_nonneg_left (heat_minimum_quarter_bound hp ht hL hb)
    (by positivity : 0 ≤ 1/Real.sqrt b)
  apply h.trans_eq
  rw [Real.sqrt_eq_rpow,one_div,← Real.rpow_neg hb.le]
  have he : -(1 : ℝ)/2+(-(1 : ℝ)/4)=-(3 : ℝ)/4 := by ring
  calc
    _ = (t^((1 : ℝ)/(2*p))*L^((1 : ℝ)/2-(1 : ℝ)/(2*p)))*
        (b^(-(1 : ℝ)/2)*b^(-(1 : ℝ)/4)) := by ring
    _ = _ := by rw [← Real.rpow_add hb,he]

theorem heat_quarter_majorant_scale_integral {t L θ : ℝ} (hL : 0 < L) :
    (∫ b in (0 : ℝ)..L^2,t^θ*L^((1 : ℝ)/2-θ)*b^(-(1 : ℝ)/4))=
      (4/3 : ℝ)*t^θ*L^(2-θ) := by
  rw [intervalIntegral.integral_const_mul,integral_quarter_heat_majorant,
    ← Real.rpow_natCast_mul hL.le]
  norm_num
  have he : (1 : ℝ)/2-θ+3/2=2-θ := by ring
  calc
    _ = (4/3 : ℝ)*t^θ*(L^((1 : ℝ)/2-θ)*L^((3 : ℝ)/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hL,he]

theorem heat_three_quarter_majorant_scale_integral {t L θ : ℝ} (hL : 0 < L) :
    (∫ b in (0 : ℝ)..L^2,t^θ*L^((1 : ℝ)/2-θ)*b^(-(3 : ℝ)/4))=
      (4 : ℝ)*t^θ*L^(1-θ) := by
  rw [intervalIntegral.integral_const_mul,integral_three_quarter_heat_majorant,
    ← Real.rpow_natCast_mul hL.le]
  norm_num
  have he : (1 : ℝ)/2-θ+1/2=1-θ := by ring
  calc
    _ = (4 : ℝ)*t^θ*(L^((1 : ℝ)/2-θ)*L^((1 : ℝ)/2)) := by ring
    _ = _ := by rw [← Real.rpow_add hL,he]

end Yau.Proofs.F03Aux
