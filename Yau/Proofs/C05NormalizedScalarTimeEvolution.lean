import Yau.Proofs.C05NormalizedScalarTimeEvolutionPhysical
import Yau.Proofs.C05NormalizedScalarTimeEvolutionClock

/-! All three intrinsic scalar sources use the same fixed normalized metric and affine clock. -/
noncomputable section
open scoped Manifold Topology ContDiff
open Set Filter
namespace Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
open Yau Yau.Blueprint Yau.Proofs.C04Aux Yau.Proofs.C05Aux Yau.Proofs.C05ThirdScalarTimeAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

def normalizedMetric (h : Flow X) (ti R : ℝ) (hR : 0 < R) (z : ℝ) :
    HermitianField X.manifold := scaleField R hR (h (ti + z / R))

theorem normalized_scalar_sources (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti + z / R) :
    deriv (fun s => scalarCurvature (h s) x) (ti + z / R) / R^2 =
      scalarTimeSource1 (normalizedMetric h ti R hR z) x ∧
    deriv (fun s => deriv (fun r => scalarCurvature (h r) x) s) (ti + z / R) / R^3 =
      scalarTimeSource2 (normalizedMetric h ti R hR z) x ∧
    deriv (fun s => deriv (fun r => deriv (fun q => scalarCurvature (h q) x) r) s)
        (ti + z / R) / R^4 = scalarTimeSource3 (normalizedMetric h ti R hR z) x :=
  ⟨normalized_scalar_first_eq_source o h U P rho hf _ R ht hR x,
    normalized_scalar_second_eq_source o h U P rho hf _ R ht hR x,
    normalized_scalar_third_eq_source o h U P rho hf _ R ht hR x⟩

theorem normalized_scalar_hasDerivAt (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti + z / R) :
    HasDerivAt (fun w => scalarCurvature (normalizedMetric h ti R hR w) x)
      (scalarTimeSource1 (normalizedMetric h ti R hR z) x) z := by
  have hd := hasDerivAt_div_pow_comp_clock R ti z hR 1
    ((scalar_contDiffAt X o h U P rho hf x ht).differentiableAt (by simp)).hasDerivAt
  have he : (fun w => scalarCurvature (normalizedMetric h ti R hR w) x) =
      (fun w => scalarCurvature (h (ti + w / R)) x / R^1) := by
    funext w
    rw [normalizedMetric, scalar_scaleField, pow_one]
    ring
  rw [he]
  exact hd.congr_deriv (normalized_scalar_sources o h U P rho hf ti R hR x z ht).1

theorem normalized_source1_hasDerivAt (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti + z / R) :
    HasDerivAt (fun w => scalarTimeSource1 (normalizedMetric h ti R hR w) x)
      (scalarTimeSource2 (normalizedMetric h ti R hR z) x) z := by
  have hc : Continuous (fun w : ℝ => ti + w / R) := continuous_const.add (continuous_id.div_const R)
  have htnear : ∀ᶠ w in 𝓝 z, 0 < ti + w / R :=
    (hc.continuousAt (x := z)).eventually (Ioi_mem_nhds ht)
  have he : (fun w => scalarTimeSource1 (normalizedMetric h ti R hR w) x) =ᶠ[𝓝 z]
      (fun w => deriv (fun s => scalarCurvature (h s) x) (ti + w / R) / R^2) := by
    filter_upwards [htnear] with w hw
    exact (normalized_scalar_sources o h U P rho hf ti R hR x w hw).1.symm
  have hd := hasDerivAt_div_pow_comp_clock R ti z hR 2
    (scalar_second_hasDerivAt o h U P rho hf x ht).differentiableAt.hasDerivAt
  exact (hd.congr_of_eventuallyEq he).congr_deriv
    (normalized_scalar_sources o h U P rho hf ti R hR x z ht).2.1

theorem normalized_source2_hasDerivAt (o : Pt X) (h : Flow X) (U P rho : STF X)
    (hf : LocalizedFlow X o h U P rho) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti + z / R) :
    HasDerivAt (fun w => scalarTimeSource2 (normalizedMetric h ti R hR w) x)
      (scalarTimeSource3 (normalizedMetric h ti R hR z) x) z := by
  have hc : Continuous (fun w : ℝ => ti + w / R) := continuous_const.add (continuous_id.div_const R)
  have htnear : ∀ᶠ w in 𝓝 z, 0 < ti + w / R :=
    (hc.continuousAt (x := z)).eventually (Ioi_mem_nhds ht)
  have he : (fun w => scalarTimeSource2 (normalizedMetric h ti R hR w) x) =ᶠ[𝓝 z]
      (fun w => deriv (fun s => deriv (fun r => scalarCurvature (h r) x) s)
        (ti + w / R) / R^3) := by
    filter_upwards [htnear] with w hw
    exact (normalized_scalar_sources o h U P rho hf ti R hR x w hw).2.1.symm
  have hd := hasDerivAt_div_pow_comp_clock R ti z hR 3
    (scalar_third_hasDerivAt_polynomial o h U P rho hf x ht).differentiableAt.hasDerivAt
  exact (hd.congr_of_eventuallyEq he).congr_deriv
    (normalized_scalar_sources o h U P rho hf ti R hR x z ht).2.2

end Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
