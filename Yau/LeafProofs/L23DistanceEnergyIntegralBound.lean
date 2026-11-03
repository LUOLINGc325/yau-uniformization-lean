import Yau.LeafProofs.L23DistanceEnergyRayIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The exact integral of the true second-variation trace yields the factor one third. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem integral_unit_sq : (∫ u in Set.Icc (0 : ℝ) 1, u^2)=(1/3 : ℝ) := by
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,integral_pow]
  norm_num

theorem integral_secondDensity_trace_bound (m K d : ℝ)
    {ι : Type*} [Fintype ι] (D : ι → ℝ → ℝ)
    (hD : ∀ i, IntegrableOn (D i) (Set.Icc (0 : ℝ) 1))
    (hTrace : ∀ u∈Set.Icc (0 : ℝ) 1, (∑ i,D i u)≤2*m+2*u^2*m*K*d^2) :
    (∑ i, ∫ u in Set.Icc (0 : ℝ) 1,D i u)≤2*m+(2/3 : ℝ)*m*K*d^2 := by
  have hp : IntegrableOn (fun u : ℝ => 2*m+2*u^2*m*K*d^2) (Set.Icc (0 : ℝ) 1) :=
    (show Continuous (fun u : ℝ => 2*m+2*u^2*m*K*d^2) by fun_prop).continuousOn.integrableOn_Icc
  have hsum : IntegrableOn (fun u => ∑ i,D i u) (Set.Icc (0 : ℝ) 1) :=
    integrable_finsetSum _ (fun i _ => hD i)
  have HI := setIntegral_mono_on hsum hp measurableSet_Icc hTrace
  rw [integral_finset_sum _ (fun i _ => hD i)] at HI
  have he : (fun u : ℝ => 2*m+2*u^2*m*K*d^2)=(fun u => 2*m+(2*m*K*d^2)*u^2) := by
    funext u
    ring
  have hc : IntegrableOn (fun _ : ℝ => 2*m) (Set.Icc (0 : ℝ) 1) := integrableOn_const (by simp)
  have hpow : IntegrableOn (fun u : ℝ => u^2) (Set.Icc (0 : ℝ) 1) :=
    (show Continuous (fun u : ℝ => u^2) by fun_prop).continuousOn.integrableOn_Icc
  rw [he,integral_add hc (hpow.const_mul (2*m*K*d^2)),
    integral_const_mul (2*m*K*d^2),integral_unit_sq] at HI
  norm_num [Measure.real] at HI
  nlinarith [HI]

end Yau.LeafProofs.L23Aux
