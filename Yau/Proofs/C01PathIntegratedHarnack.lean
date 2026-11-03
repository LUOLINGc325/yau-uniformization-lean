import Yau.Proofs.C01PathWeightedMonotonicity

/-! Endpoint evaluation of the genuine path integrating factor. -/

noncomputable section

open MeasureTheory
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_path_integrated_harnack
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    {x₀ x₁ : Pt X} (γ : PiecewiseC1Curve x₀ x₁) (a b ε : ℝ)
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε)
    (hv : Continuous (curveSpeed (h a) γ))
    (hγc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ContinuousAt γ.toFun s)
    (hγd : ∀ s ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ
      (fun u : ℝ => extChartAt (ComplexModel n) (γ s) (γ u)) s) :
    scalarCurvature (h a) x₀ ≤ scalarCurvature (h b) x₁ * (b / a) *
      Real.exp ((curveLength (h a) γ + ε) * curveLength (h a) γ / (b - a)) := by
  let v := curveSpeed (h a) γ
  let L := curveLength (h a) γ
  have hL : speedPrimitive v 1 = L := by
    rw [speedPrimitive, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc]
    rfl
  have hLnonneg : 0 ≤ speedPrimitive v 1 :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => Real.sqrt_nonneg _)
  have hq : speedPrimitive v 1 + ε ≠ 0 := (add_pos_of_nonneg_of_pos hLnonneg hε).ne'
  have hclock := regularizedTimeClock_one hv a b ε hq
  have hcost : regularizedPathCost v a b ε 1 = (L + ε) * L / (b - a) := by
    dsimp only [regularizedPathCost]
    rw [hL]
    ring
  have hzero : scalarPathWeight h γ a b ε 0 = a * scalarCurvature (h a) x₀ := by
    change regularizedTimeClock v a b ε 0 *
      scalarCurvature (h (regularizedTimeClock v a b ε 0)) (γ 0) *
        Real.exp (regularizedPathCost v a b ε 0) = _
    rw [regularizedTimeClock_zero, γ.start_eq]
    simp only [regularizedPathCost, speedPrimitive, intervalIntegral.integral_same,
      mul_zero, Real.exp_zero, mul_one]
  have hone : scalarPathWeight h γ a b ε 1 =
      b * scalarCurvature (h b) x₁ * Real.exp ((L + ε) * L / (b - a)) := by
    change regularizedTimeClock v a b ε 1 *
      scalarCurvature (h (regularizedTimeClock v a b ε 1)) (γ 1) *
        Real.exp (regularizedPathCost v a b ε 1) = _
    rw [hclock, γ.finish_eq, hcost]
  have hm := localizedFlow_scalar_path_weight_monotoneOn hflow hjoint γ a b ε ha hab hε hv hγc hγd
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) zero_le_one
  rw [hzero, hone] at hm
  have heq : scalarCurvature (h b) x₁ * (b / a) * Real.exp ((L + ε) * L / (b - a)) =
      (b * scalarCurvature (h b) x₁ * Real.exp ((L + ε) * L / (b - a))) / a := by
    field_simp [ha.ne']
    <;> ring
  change scalarCurvature (h a) x₀ ≤
    scalarCurvature (h b) x₁ * (b / a) * Real.exp ((L + ε) * L / (b - a))
  rw [heq]
  apply (le_div_iff₀ ha).mpr
  simpa only [mul_comm a] using hm

end Yau.NodeProofs.C01Aux
