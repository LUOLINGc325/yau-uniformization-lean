import Yau.Proofs.F03KernelTerminalDomination
import Yau.Proofs.F03RegularClosedMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine product integrability permits space and physical time to be exchanged for the actual potential. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletMinimalKernel_U_eq_integral_P
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (x : Pt X) {s : ℝ} (hs : s ∈ Icc 0 T) :
    (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*U y s ∂μ)=
      ∫ r in (0:ℝ)..s,∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*P y r ∂μ := by
  letI : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite X.metric μ hμ
  let ν : Measure (Ioc (0:ℝ) s) := volume.comap Subtype.val
  have hFin : (volume : Measure ℝ) (Ioc 0 s) < ⊤ :=
    (measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top
  letI : IsFiniteMeasure ν := comap_subtype_isFiniteMeasure_of_measure_lt_top volume
    (Ioc (0:ℝ) s) measurableSet_Ioc hFin
  let k := dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x
  have hk := kernelSmooth_univ_continuous_right _
    (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO) hb x
  have hTime (y : Pt X) : Continuous (fun r : Ioc (0:ℝ) s => P y r.val) :=
    continuousOn_iff_continuous_restrict.mp ((F02Aux.timeSlice_continuousOn hf.2.2.1 y).mono
      (show Ioc (0:ℝ) s ⊆ Ici 0 from fun r hr => hr.1.le))
  have hMeas : Measurable (fun p : Ioc (0:ℝ) s × Pt X => k p.2*P p.2 p.1.val) := by
    change Measurable (Function.uncurry (fun (r : Ioc (0:ℝ) s) (y : Pt X) => k y*P y r.val))
    exact measurable_uncurry_of_continuous_of_measurable
      (fun y => continuous_const.mul (hTime y))
      (fun r => hk.measurable.mul (continuous_of_smoothFn
        (LeafProofs.L19Aux.smoothSpaceTime_slice hf.2.2.1 r.property.1.le)).measurable)
  have hDom := dirichletMinimalKernel_terminal_density_integrable X o h U P ρ hf hT μ hμ O hO hb x
  have hDomProd : Integrable (fun p : Ioc (0:ℝ) s × Pt X => k p.2*ρ p.2 T) (ν.prod μ) := by
    simpa only [one_mul] using (integrable_const (1:ℝ) : Integrable (fun _ : Ioc (0:ℝ) s => (1:ℝ)) ν).mul_prod hDom
  have hProduct : Integrable (fun p : Ioc (0:ℝ) s × Pt X => k p.2*P p.2 p.1.val) (ν.prod μ) := by
    apply hDomProd.mono' hMeas.aestronglyMeasurable
    apply ae_of_all (ν.prod μ)
    intro p
    have hk0 : 0 ≤ k p.2 := dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb x p.2
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_left
      (localizedFlow_potential_time_envelope X o h U P ρ hf
        ⟨p.1.property.1.le,p.1.property.2.trans hs.2⟩ p.2).1 hk0
  have hSwap := integral_integral_swap (f := fun (r : Ioc (0:ℝ) s) (y : Pt X) => k y*P y r.val) hProduct
  calc
    _ = ∫ y,∫ r : Ioc (0:ℝ) s,k y*P y r.val ∂ν ∂μ := by
      apply integral_congr_ae
      apply ae_of_all μ
      intro y
      change k y*U y s=∫ r : Ioc (0:ℝ) s,k y*P y r.val ∂ν
      rw [F02Aux.potential_eq_integral_P X o h U P ρ hf hs.1 y,
        ← intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le hs.1]
      exact (integral_subtype_comap measurableSet_Ioc (fun r : ℝ => k y*P y r)).symm
    _ = ∫ r : Ioc (0:ℝ) s,∫ y,k y*P y r.val ∂μ ∂ν := hSwap.symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le hs.1]
      exact integral_subtype_comap measurableSet_Ioc (fun r : ℝ => ∫ y,k y*P y r ∂μ)

end Yau.Proofs.F03Aux
