import Yau.Proofs.C05NormalizedHarnackTimeDerivatives

/-! The actual normalized Harnack sum is smooth on its original positive
physical-time domain; its second derivative is the computed intrinsic source. -/
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux Yau.Proofs.C05NormalizedScalarTimeEvolutionAux
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem scalarHarnackSum_contDiffAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun s => scalarHarnackSum h x s) t := by
  have hr := scalar_contDiffAt X o h U P ρ hf x ht
  exact (hr.derivWithin (by simp)).add ((contDiffAt_id.inv ht.ne').mul hr)

theorem normalized_scalarHarnack_contDiffAt (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti+z/R) :
    ContDiffAt ℝ ∞ (fun w => scalarHarnackSource (normalizedMetric h ti R hR w) (ti*R+w)⁻¹ x) z := by
  have hc : ContDiffAt ℝ ∞ (fun w : ℝ => ti+w/R) z :=
    contDiffAt_const.add (contDiffAt_id.div_const R)
  have hs := ((scalarHarnackSum_contDiffAt o h U P ρ hf x ht).comp z hc).div_const (R^2)
  have hclock : Continuous (fun w : ℝ => ti+w/R) := continuous_const.add (continuous_id.div_const R)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hclock.continuousAt.eventually (Ioi_mem_nhds ht)] with w hw
  exact (normalizedScalarHarnackSum_eq_source o h U P ρ hf ti R hR x w hw).symm

theorem normalized_scalarHarnack_iteratedDeriv_two (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (ti R : ℝ) (hR : 0 < R)
    (x : Pt X) (z : ℝ) (ht : 0 < ti+z/R) :
    iteratedDeriv 2 (fun w => scalarHarnackSource (normalizedMetric h ti R hR w) (ti*R+w)⁻¹ x) z =
      intrinsicScalarHarnackSecondTime (normalizedMetric h ti R hR z) (ti*R+z)⁻¹ x := by
  have hc : Continuous (fun w : ℝ => ti+w/R) := continuous_const.add (continuous_id.div_const R)
  have he : (fun w => deriv (fun u => scalarHarnackSource
      (normalizedMetric h ti R hR u) (ti*R+u)⁻¹ x) w) =ᶠ[𝓝 z]
      (fun w => intrinsicScalarHarnackTime (normalizedMetric h ti R hR w) (ti*R+w)⁻¹ x) := by
    filter_upwards [hc.continuousAt.eventually (Ioi_mem_nhds ht)] with w hw
    exact (normalized_scalarHarnack_hasDerivAt o h U P ρ hf ti R hR x w hw).deriv
  have hd := (normalized_scalarHarnackTime_hasDerivAt o h U P ρ hf ti R hR x z ht).congr_of_eventuallyEq he
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hd.deriv

theorem normalized_scalarHarnack_nonneg (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (ti R : ℝ) (hR : 0 < R) (x : Pt X) (z : ℝ) (ht : 0 < ti+z/R) :
    0 ≤ scalarHarnackSource (normalizedMetric h ti R hR z) (ti*R+z)⁻¹ x := by
  have hs := (scalarHarnack_minimized o h hH x ht).1.trans
    (scalarHarnack_minimized o h hH x ht).2
  change 0 ≤ scalarHarnackSource (scaleField R hR (h (ti+z/R))) (ti*R+z)⁻¹ x
  rw [← normalizedScalarHarnackSum_eq_source o h U P ρ hf ti R hR x z ht]
  exact div_nonneg hs (sq_nonneg R)

end Yau.Proofs.C05Aux
