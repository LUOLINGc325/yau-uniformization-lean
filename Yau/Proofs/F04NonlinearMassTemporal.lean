import Yau.Proofs.F04NonlinearMassPointwise
import Yau.Proofs.F04FiniteMassTemporal

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.LeafProofs.L18Aux

/-- The actual nonlinear exponential mass obeys the same finite-cutoff
 spatial/time bound. The spatial test is w, and w<=exp(w)-1 transports its
 main term to the genuine exponential mass. No initial smoothness of w
 or global integrability is required. -/
theorem finite_nonlinear_mass_time_bound
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T t R a C : ℝ} (ht : t ∈ Ioo 0 T)
    (μg μt : Measure (Pt X)) (hμg : IsRiemannianVolume X.metric.form μg)
    (hμt : IsRiemannianVolume (h t) μt) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) (hR : 0 < R)
    {w χ : STF X} (hw : SmoothSpaceTime w (Ioo 0 T)) (hχ : SmoothSpaceC1Time χ (Icc 0 T))
    (hC : 0 ≤ C) (hw0 : ∀ x, 0 ≤ w x t) (hχ0 : ∀ x, 0 ≤ χ x t)
    (hχt : ∀ x, deriv (χ x) t ≤ a*χ x t)
    (hEq : ∀ x, deriv (w x) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
      (1-Real.exp (-w x t))*scalarCurvature (h t) x)
    (hLevi : ∀ x, HermLE (levi (fun y => χ y t) x) (((C*χ x t : ℝ) : ℂ) • gMat (h t) x))
    (hErr : Integrable (fun x => |w x t*massScalarError (h t) u (fun y => χ y t) R x*density ρ x t|) μg) :
    (∫ x, massCutoff u R x*
      ((deriv (fun s => Real.exp (w x s)-1) t*χ x t+(Real.exp (w x t)-1)*deriv (χ x) t)*density ρ x t-
        scalarCurvature (h t) x*((Real.exp (w x t)-1)*χ x t*density ρ x t)) ∂μg) ≤
      ((n : ℝ)*C+a)*(∫ x, massCutoff u R x*((Real.exp (w x t)-1)*χ x t*density ρ x t) ∂μg)+
        ∫ x, |w x t*massScalarError (h t) u (fun y => χ y t) R x*density ρ x t| ∂μg := by
  let z : STF X := fun x s => Real.exp (w x s)-1
  have hwc := smoothSpaceTime_c1 hw
  have hzc : SmoothSpaceC1Time z (Ioo 0 T) := smoothSpaceTime_c1 (fun c => (hw c).exp.sub contDiffOn_const)
  have htC := Ioo_subset_Icc_self ht
  have hd : SmoothSpaceC1Time (density ρ) (Icc 0 T) :=
    smoothSpaceTime_c1 ((massVolumeTransport o h U P ρ hloc T (lt_trans ht.1 ht.2)).1)
  have hpC := continuous_of_smoothFn (massCutoff_smooth hu.1 R)
  have hwC := continuous_of_smoothFn (hwc.1 t ht)
  have hzC := continuous_of_smoothFn (hzc.1 t ht)
  have hχC := continuous_of_smoothFn (hχ.1 t htC)
  have hdC := continuous_of_smoothFn (hd.1 t htC)
  have hzDC := c1_timeDerivative_slice_continuous isOpen_Ioo hzc ht
  have hχDC := c1_timeDerivative_slice_continuous isOpen_Ioo
    (smoothSpaceC1Time_mono hχ Ioo_subset_Icc_self) ht
  have hRC := flow_scalarCurvature_slice_continuous X o h U P ρ hloc ht.1
  have hlapC := continuous_of_smoothFn (Adjoint.smoothFn_laplacian (h t)
    (metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht.1.le) (hwc.1 t ht))
  have hc := massCutoff_compact X o u hu hR
  have hIZ : Integrable (fun x => massCutoff u R x*(z x t*χ x t*density ρ x t)) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      (hpC.mul ((hzC.mul hχC).mul hdC)) hc.mul_right
  have hIW : Integrable (fun x => massCutoff u R x*(w x t*χ x t*density ρ x t)) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      (hpC.mul ((hwC.mul hχC).mul hdC)) hc.mul_right
  have hJ : Integrable (fun x => massCutoff u R x*
      ((deriv (z x) t*χ x t+z x t*deriv (χ x) t)*density ρ x t-
        scalarCurvature (h t) x*(z x t*χ x t*density ρ x t))) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      (hpC.mul ((((hzDC.mul hχC).add (hzC.mul hχDC)).mul hdC).sub (hRC.mul ((hzC.mul hχC).mul hdC)))) hc.mul_right
  have hS : Integrable (fun x => (χ x t*massCutoff u R x*laplacian (h t) (fun y => w y t) x)*density ρ x t) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      (((hχC.mul hpC).mul hlapC).mul hdC) hc.mul_left.mul_right.mul_right
  have hTime := integral_mono hJ (hS.add (hIZ.const_mul a))
    (nonlinear_compact_mass_pointwise X h ρ u w χ
      (fun x => smoothSpaceC1Time_hasDerivAt isOpen_Ioo hwc x ht) hEq hw0 hχt)
  simp only [Pi.add_apply] at hTime
  rw [integral_add hS (hIZ.const_mul a),integral_const_mul] at hTime
  have hSpace := finite_mass_spatial_bound X o h U P ρ hloc μg μt hμg hμt ht.1.le u hu hR
    (hχ.1 t htC) (hwc.1 t ht) hw0 C hLevi hErr
  have hCompare : (∫ x, massCutoff u R x*(w x t*χ x t*density ρ x t) ∂μg) ≤
      ∫ x, massCutoff u R x*(z x t*χ x t*density ρ x t) ∂μg := by
    apply integral_mono hIW hIZ
    intro x
    have he := mul_le_mul_of_nonneg_left (self_le_exponential_sub_one (w x t))
      (mul_nonneg (mul_nonneg (massCutoff_range u R x).1 (hχ0 x)) (density_pos ρ x t).le)
    change massCutoff u R x*(w x t*χ x t*density ρ x t) ≤ massCutoff u R x*((Real.exp (w x t)-1)*χ x t*density ρ x t)
    nlinarith only [he]
  have hMain := mul_le_mul_of_nonneg_left hCompare (mul_nonneg (Nat.cast_nonneg n) hC)
  change (∫ x, massCutoff u R x*((deriv (z x) t*χ x t+z x t*deriv (χ x) t)*density ρ x t-
      scalarCurvature (h t) x*(z x t*χ x t*density ρ x t)) ∂μg) ≤ _
  nlinarith only [hTime,hSpace,hMain]

end Yau.F04Proof
