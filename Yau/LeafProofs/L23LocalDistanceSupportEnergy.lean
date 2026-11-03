import Yau.LeafProofs.L23LocalDistanceSupportEscape

/-! The actual path energy bounds squared project distance. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

set_option backward.isDefEq.respectTransparency false in
theorem unit_interval_integral_sq_le {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) 1))
    (hf2 : IntegrableOn (fun s => f s ^ 2) (Set.Icc (0 : ℝ) 1)) :
    (∫ s in Set.Icc (0 : ℝ) 1, f s)^2 ≤ ∫ s in Set.Icc (0 : ℝ) 1, f s ^ 2 := by
  let L := ∫ s in Set.Icc (0 : ℝ) 1, f s
  have hconst : IntegrableOn (fun _ : ℝ => L^2) (Set.Icc (0 : ℝ) 1) := integrableOn_const (hs := by simp)
  have heq : (fun s => (f s-L)^2) = (fun s => f s^2-(2*L)*f s+L^2) := by
    funext s
    ring
  have H : 0 ≤ ∫ s in Set.Icc (0 : ℝ) 1, (f s-L)^2 := integral_nonneg fun _ => sq_nonneg _
  rw [heq] at H
  have hlinear : IntegrableOn (fun s => f s^2-(2*L)*f s) (Set.Icc (0 : ℝ) 1) :=
    hf2.sub (hf.const_mul (2*L))
  have hadd : (∫ s in Set.Icc (0 : ℝ) 1, f s^2-(2*L)*f s+L^2) =
      (∫ s in Set.Icc (0 : ℝ) 1, f s^2-(2*L)*f s) +
        ∫ s in Set.Icc (0 : ℝ) 1, L^2 := integral_add hlinear hconst
  have hsub : (∫ s in Set.Icc (0 : ℝ) 1, f s^2-(2*L)*f s) =
      (∫ s in Set.Icc (0 : ℝ) 1, f s^2) -
        ∫ s in Set.Icc (0 : ℝ) 1, (2*L)*f s := integral_sub hf2 (hf.const_mul (2*L))
  rw [hadd,hsub,integral_const_mul] at H
  simp only [integral_const,smul_eq_mul] at H
  norm_num [Measure.real] at H
  change 0 ≤ (∫ s in Set.Icc (0 : ℝ) 1, f s^2) - (2*L)*L + L^2 at H
  change L^2 ≤ ∫ s in Set.Icc (0 : ℝ) 1, f s^2
  nlinarith only [H]

def fieldPathEnergy (h : HermitianField M) (γ : ℝ → M.Carrier) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) 1, fieldPathSpeed h γ s ^ 2

theorem fieldPathSpeed_sq (h : HermitianField M) (γ : ℝ → M.Carrier) (s : ℝ) :
    fieldPathSpeed h γ s ^ 2 = 2*hermitianNormSq (h (γ s))
      (realTangentEquiv (γ s) (realCurveVelocity γ s)) :=
  Real.sq_sqrt (mul_nonneg (by norm_num) (hermitianNormSq_nonneg _ _))

theorem fieldPathEnergy_eq_integral_metric (h : HermitianField M) (γ : ℝ → M.Carrier) :
    fieldPathEnergy h γ = ∫ s in Set.Icc (0 : ℝ) 1,
      2*hermitianNormSq (h (γ s)) (realTangentEquiv (γ s) (realCurveVelocity γ s)) := by
  apply integral_congr_ae
  exact Eventually.of_forall (fieldPathSpeed_sq h γ)

theorem fieldPathELength_eq_ofReal_integral (h : HermitianField M) (γ : ℝ → M.Carrier)
    (hγ : IntegrableOn (fieldPathSpeed h γ) (Set.Icc (0 : ℝ) 1)) :
    fieldPathELength h γ 0 1 = ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) 1, fieldPathSpeed h γ s) := by
  rw [fieldPathELength_eq_lintegral]
  exact (ofReal_integral_eq_lintegral_ofReal hγ
    (Eventually.of_forall fun _ => Real.sqrt_nonneg _)).symm

theorem inducedDistance_sq_le_fieldPathEnergy (h : HermitianField M) (hh : MetricSmooth h)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y)
    (hγ : IntegrableOn (fieldPathSpeed h γ) (Set.Icc (0 : ℝ) 1))
    (hγ2 : IntegrableOn (fun s => fieldPathSpeed h γ s ^ 2) (Set.Icc (0 : ℝ) 1)) :
    inducedDistance h x y ^ 2 ≤ fieldPathEnergy h γ := by
  have H := inducedDistance_le_fieldPathELength_piecewise h hh γ
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
  rw [γ.finish_eq,fieldPathELength_eq_ofReal_integral h γ hγ] at H
  have hnonneg : 0 ≤ ∫ s in Set.Icc (0 : ℝ) 1, fieldPathSpeed h γ s :=
    integral_nonneg fun _ => Real.sqrt_nonneg _
  have Hreal := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp H
  exact ((sq_le_sq₀ (inducedDistance_nonneg h hh x y) hnonneg).mpr Hreal).trans
    (unit_interval_integral_sq_le hγ hγ2)

end Yau.LeafProofs.L23Aux
