import Yau.Proofs.F04FiniteMassSpatial
import Yau.Proofs.F04SubcaloricAlgebra

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint Yau.LeafProofs.L18Aux

theorem finite_subcaloric_mass_time_bound {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T t R a C : ℝ} (ht : t ∈ Ioo 0 T)
    (μg μt : Measure (Pt X)) (hμg : IsRiemannianVolume X.metric.form μg)
    (hμt : IsRiemannianVolume (h t) μt)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) (hR : 0 < R)
    {z χ : STF X} (hz : SmoothSpaceTime z (Icc 0 T))
    (hχ : SmoothSpaceC1Time χ (Icc 0 T))
    (hcal : ∀ x, heatOp h (Icc 0 T) z x t ≤ 0)
    (hz0 : ∀ x, 0 ≤ z x t) (hχ0 : ∀ x, 0 ≤ χ x t)
    (hχt : ∀ x, deriv (χ x) t ≤ a * χ x t)
    (hLevi : ∀ x, HermLE (levi (fun y => χ y t) x)
      (((C * χ x t : ℝ) : ℂ) • gMat (h t) x))
    (hErr : Integrable (fun x => |z x t * massScalarError (h t) u (fun y => χ y t) R x *
      density ρ x t|) μg) :
    (∫ x, massCutoff u R x *
      ((deriv (z x) t * χ x t + z x t * deriv (χ x) t) * density ρ x t -
        scalarCurvature (h t) x * (z x t * χ x t * density ρ x t)) ∂μg) ≤
      ((n : ℝ) * C + a) * (∫ x, massCutoff u R x * (z x t * χ x t * density ρ x t) ∂μg) +
        ∫ x, |z x t * massScalarError (h t) u (fun y => χ y t) R x * density ρ x t| ∂μg := by
  have htC : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hzc := smoothSpaceTime_c1 hz
  have hd : SmoothSpaceC1Time (density ρ) (Icc 0 T) :=
    smoothSpaceTime_c1 ((massVolumeTransport o h U P ρ hloc T (lt_trans ht.1 ht.2)).1)
  have hpC := continuous_of_smoothFn (massCutoff_smooth hu.1 R)
  have hzC := continuous_of_smoothFn (hzc.1 t htC)
  have hχC := continuous_of_smoothFn (hχ.1 t htC)
  have hdC := continuous_of_smoothFn (hd.1 t htC)
  have hzDC := c1_timeDerivative_slice_continuous isOpen_Ioo
    (smoothSpaceC1Time_mono hzc Ioo_subset_Icc_self) ht
  have hχDC := c1_timeDerivative_slice_continuous isOpen_Ioo
    (smoothSpaceC1Time_mono hχ Ioo_subset_Icc_self) ht
  have hRC := flow_scalarCurvature_slice_continuous X o h U P ρ hloc ht.1
  have hlapC := continuous_of_smoothFn (Adjoint.smoothFn_laplacian (h t)
    (metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht.1.le) (hzc.1 t htC))
  have hc := massCutoff_compact X o u hu hR
  have hI : Integrable (fun x => massCutoff u R x * (z x t * χ x t * density ρ x t)) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      (hpC.mul ((hzC.mul hχC).mul hdC)) hc.mul_right
  have hJ : Integrable (fun x => massCutoff u R x *
      ((deriv (z x) t * χ x t + z x t * deriv (χ x) t) * density ρ x t -
        scalarCurvature (h t) x * (z x t * χ x t * density ρ x t))) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      (hpC.mul ((((hzDC.mul hχC).add (hzC.mul hχDC)).mul hdC).sub (hRC.mul ((hzC.mul hχC).mul hdC))))
      hc.mul_right
  have hS : Integrable (fun x => (χ x t * massCutoff u R x *
      laplacian (h t) (fun y => z y t) x) * density ρ x t) μg :=
    initial_volume_integrable_of_continuous_compact X.metric μg hμg
      (((hχC.mul hpC).mul hlapC).mul hdC) hc.mul_left.mul_right.mul_right
  have htime := integral_mono hJ (hS.add (hI.const_mul a))
    (subcaloric_compact_mass_pointwise X o h U P ρ hloc ht u z χ hcal hz0 hχ0 hχt)
  simp only [Pi.add_apply] at htime
  rw [integral_add hS (hI.const_mul a), integral_const_mul] at htime
  have hspace := finite_mass_spatial_bound X o h U P ρ hloc μg μt hμg hμt ht.1.le u hu hR
    (hχ.1 t htC) (hzc.1 t htC) hz0 C hLevi hErr
  nlinarith only [htime, hspace]

end Yau.F04Proof
