import Yau.Proofs.C05NormalizedInverseEnergyDerivative

/-! Actual first and second affine-clock derivatives of the original
normalized Harnack sum and the actual minimized Harnack function. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux
open Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {M : ComplexManifold n} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

def intrinsicScalarHarnackTime (k : HermitianField M) (κ : ℝ) (x : M.Carrier) : ℝ :=
  scalarTimeSource2 k x + κ*scalarTimeSource1 k x - κ^2*scalarCurvature k x

def intrinsicScalarHarnackSecondTime (k : HermitianField M) (κ : ℝ) (x : M.Carrier) : ℝ :=
  scalarTimeSource3 k x + κ*scalarTimeSource2 k x -
    2*κ^2*scalarTimeSource1 k x + 2*κ^3*scalarCurvature k x

theorem normalized_clock_inverse_hasDerivAt (ti R z : ℝ) (hR : 0 < R)
    (ht : 0 < ti+z/R) :
    HasDerivAt (fun w : ℝ => (ti*R+w)⁻¹) (-((ti*R+z)⁻¹)^2) z := by
  have hc : ti*R+z = R*(ti+z/R) := by field_simp [hR.ne'] <;> ring
  have hn : ti*R+z ≠ 0 := (show 0 < ti*R+z by rw [hc]; positivity).ne'
  simpa only [Function.comp_def,mul_one,inv_pow] using
    (hasDerivAt_inv hn).comp z ((hasDerivAt_id z).const_add (ti*R))

theorem normalized_scalarHarnack_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti+z/R) :
    HasDerivAt (fun w => scalarHarnackSource (normalizedMetric h ti R hR w) (ti*R+w)⁻¹ x)
      (intrinsicScalarHarnackTime (normalizedMetric h ti R hR z) (ti*R+z)⁻¹ x) z := by
  have h0 := normalized_scalar_hasDerivAt o h U P ρ hf ti R hR x z ht
  have h1 := normalized_source1_hasDerivAt o h U P ρ hf ti R hR x z ht
  have hc := normalized_clock_inverse_hasDerivAt ti R z hR ht
  have hd := h1.add (hc.mul h0)
  have he : (fun w => scalarTimeSource1 (normalizedMetric h ti R hR w) x +
      (ti*R+w)⁻¹*scalarCurvature (normalizedMetric h ti R hR w) x) =
      (fun w => scalarHarnackSource (normalizedMetric h ti R hR w) (ti*R+w)⁻¹ x) := by
    funext w
    simp only [scalarTimeSource1,scalarHarnackSource,zero_mul,add_zero]
  change HasDerivAt (fun w => scalarTimeSource1 (normalizedMetric h ti R hR w) x +
    (ti*R+w)⁻¹*scalarCurvature (normalizedMetric h ti R hR w) x) _ z at hd
  rw [he] at hd
  apply hd.congr_deriv
  dsimp [intrinsicScalarHarnackTime]
  ring

theorem normalized_scalarHarnackTime_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti+z/R) :
    HasDerivAt (fun w => intrinsicScalarHarnackTime (normalizedMetric h ti R hR w) (ti*R+w)⁻¹ x)
      (intrinsicScalarHarnackSecondTime (normalizedMetric h ti R hR z) (ti*R+z)⁻¹ x) z := by
  have h0 := normalized_scalar_hasDerivAt o h U P ρ hf ti R hR x z ht
  have h1 := normalized_source1_hasDerivAt o h U P ρ hf ti R hR x z ht
  have h2 := normalized_source2_hasDerivAt o h U P ρ hf ti R hR x z ht
  have hc := normalized_clock_inverse_hasDerivAt ti R z hR ht
  have hd := (h2.add (hc.mul h1)).sub ((hc.pow 2).mul h0)
  change HasDerivAt (fun w => intrinsicScalarHarnackTime (normalizedMetric h ti R hR w) (ti*R+w)⁻¹ x) _ z at hd
  apply hd.congr_deriv
  dsimp [intrinsicScalarHarnackSecondTime]
  ring

theorem normalized_minimum_hasDerivAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (ti R : ℝ) (hR : 0 < R) (x : Pt X) (z : ℝ) (ht : 0 < ti+z/R) :
    HasDerivAt (fun w => normalizedHarnackMinimum h ti R x w)
      (intrinsicScalarHarnackTime (normalizedMetric h ti R hR z) (ti*R+z)⁻¹ x -
        intrinsicInverseEnergyTime (normalizedMetric h ti R hR z) x) z := by
  have hd := (normalized_scalarHarnack_hasDerivAt o h U P ρ hf ti R hR x z ht).sub
    (normalized_inverseEnergy_hasDerivAt o h U P ρ hf hH ti R hR x z ht)
  have hc : Continuous (fun w : ℝ => ti+w/R) := continuous_const.add (continuous_id.div_const R)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds ht)] with w hw
  exact normalizedHarnackMinimum_eq_intrinsic o h U P ρ hf hH ti R hR x w hw

end Yau.Proofs.C05Aux
