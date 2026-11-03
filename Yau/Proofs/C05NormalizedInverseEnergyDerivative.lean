import Yau.Proofs.C05NormalizedInverseEnergyTime

/-! Actual affine-clock differentiation of the inverse energy of the same
normalized metric, with no time choice of charts or auxiliary solution. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux Yau.LeafProofs
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem normalized_inverseEnergy_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (ti R : ℝ) (hR : 0 < R) (x : Pt X) (z : ℝ) (ht : 0 < ti+z/R) :
    HasDerivAt (fun w => realRicciDifferentialEnergy (normalizedMetric h ti R hR w)
      (scalarCurvature (normalizedMetric h ti R hR w)) x)
      (intrinsicInverseEnergyTime (normalizedMetric h ti R hR z) x) z := by
  have hd := hasDerivAt_div_pow_comp_clock R ti z hR 2
    (realRicciDifferentialEnergy_hasDerivAt o h U P ρ hf hH x ht)
  have hc : Continuous (fun w : ℝ => ti+w/R) := continuous_const.add (continuous_id.div_const R)
  have he : (fun w => realRicciDifferentialEnergy (normalizedMetric h ti R hR w)
      (scalarCurvature (normalizedMetric h ti R hR w)) x) =ᶠ[𝓝 z]
      (fun w => realRicciDifferentialEnergy (h (ti+w/R))
        (scalarCurvature (h (ti+w/R))) x / R^2) := by
    filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds ht)] with w hw
    have hk := L23Aux.metricFamilySmooth_slice h hf.1.2.1 (show 0 ≤ ti+w/R from hw.le)
    have hK := hf.1.2.2.1 (ti+w/R) hw.le
    rw [normalizedMetric,realRicciDifferentialEnergy_scaled_scalar R hR _ hk hK]
    ring
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  exact normalized_ricciDifferentialEnergyTime_eq o h U P ρ hf (ti+z/R) R ht hR x

end Yau.Proofs.C05Aux
