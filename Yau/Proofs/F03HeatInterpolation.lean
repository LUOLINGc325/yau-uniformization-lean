import Yau.Proofs.F03HeatScaleNumerics

/-! Fractional interpolation keeps both scalar and gradient heat-time majorants integrable at zero. -/
noncomputable section
open MeasureTheory Set
open scoped Interval
namespace Yau.Proofs.F03Aux

theorem quarter_heat_majorant_integrable (R : ℝ) :
    IntervalIntegrable (fun b : ℝ => b^(-(1 : ℝ)/4)) volume 0 R ∧
      IntervalIntegrable (fun b : ℝ => b^(-(3 : ℝ)/4)) volume 0 R := by
  exact ⟨intervalIntegral.intervalIntegrable_rpow' (by norm_num),intervalIntegral.intervalIntegrable_rpow' (by norm_num)⟩

theorem integral_quarter_heat_majorant (R : ℝ) :
    (∫ b in (0 : ℝ)..R,b^(-(1 : ℝ)/4))=(4/3 : ℝ)*R^((3 : ℝ)/4) := by
  calc
    _ = (R^(-(1 : ℝ)/4+1)-(0 : ℝ)^(-(1 : ℝ)/4+1))/(-(1 : ℝ)/4+1) :=
      integral_rpow (Or.inl (by norm_num))
    _ = _ := by norm_num;ring

theorem integral_three_quarter_heat_majorant (R : ℝ) :
    (∫ b in (0 : ℝ)..R,b^(-(3 : ℝ)/4))=(4 : ℝ)*R^((1 : ℝ)/4) := by
  calc
    _ = (R^(-(3 : ℝ)/4+1)-(0 : ℝ)^(-(3 : ℝ)/4+1))/(-(3 : ℝ)/4+1) :=
      integral_rpow (Or.inl (by norm_num))
    _ = _ := by norm_num;ring

end Yau.Proofs.F03Aux
