import Yau.LeafProofs.L05ABPMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

/-- Reverse Fatou is applied only to measurable source densities; an exceptional
set in the a.e. upper bound never enters an image under the contact map. -/
theorem integral_reverseFatou_bound {E : Type*} [MeasurableSpace E] {mu : Measure E}
    {f : ℕ → E → ℝ} {M G : E → ℝ} {a : ℕ → ℝ} {A : ℝ}
    (hf : ∀ j, Measurable (f j)) (hfn : ∀ j, 0 ≤ᵐ[mu] f j)
    (hfi : ∀ j, Integrable (f j) mu) (hM : Integrable M mu) (hMn : 0 ≤ᵐ[mu] M)
    (hbound : ∀ j, f j ≤ᵐ[mu] M) (hG : Integrable G mu) (hGn : 0 ≤ᵐ[mu] G)
    (hlim : ∀ᵐ z ∂mu, limsup (fun j => ENNReal.ofReal (f j z)) atTop ≤ ENNReal.ofReal (G z))
    (ha : Tendsto a atTop (𝓝 A)) (hale : ∀ j, a j ≤ ∫ z, f j z ∂mu) :
    A ≤ ∫ z, G z ∂mu := by
  have hfin : (∫⁻ z, ENNReal.ofReal (M z) ∂mu) ≠ (⊤ : ENNReal) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hM hMn]
    exact ENNReal.ofReal_ne_top
  have hj (j : ℕ) : ENNReal.ofReal (a j) ≤ ∫⁻ z, ENNReal.ofReal (f j z) ∂mu := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi j) (hfn j)]
    exact ENNReal.ofReal_le_ofReal (hale j)
  have ham : Tendsto (fun j => ENNReal.ofReal (a j)) atTop (𝓝 (ENNReal.ofReal A)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp ha
  have hlow := limsup_le_limsup (f := atTop) (Filter.Eventually.of_forall hj)
  rw [ham.limsup_eq] at hlow
  have hrev := limsup_lintegral_le (fun z => ENNReal.ofReal (M z))
    (fun j => ENNReal.measurable_ofReal.comp (hf j))
    (fun j => (hbound j).mono fun z hz => ENNReal.ofReal_le_ofReal hz) hfin
  have hfinal := hlow.trans (hrev.trans (lintegral_mono_ae hlim))
  rw [← ofReal_integral_eq_lintegral_ofReal hG hGn] at hfinal
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hGn)).mp hfinal

def smoothContactDensity {n : ℕ} (R a b : ℝ) (u : Point n → ℝ) : Point n → ℝ :=
  (smoothContact R a b u).indicator (fun z => |(fderiv ℝ (contactMap u) z).det|)

theorem smoothContactDensity_nonneg {n : ℕ} (R a b : ℝ) (u : Point n → ℝ) (z : Point n) :
    0 ≤ smoothContactDensity R a b u z := by
  exact Set.indicator_nonneg (fun z _ => abs_nonneg _) z

theorem smoothContactDensity_measurable {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) : Measurable (smoothContactDensity R a b u) := by
  have hc : Continuous (fun z => |(fderiv ℝ (contactMap u) z).det|) :=
    (ContinuousLinearMap.continuous_det.comp
      ((contactMap_smooth hu).continuous_fderiv (by simp))).abs
  exact hc.measurable.indicator (smoothContact_measurable hu)

theorem smoothContactDensity_integrable {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hu : ContDiff ℝ ∞ u) : Integrable (smoothContactDensity R a b u) := by
  exact (integrable_indicator_iff (smoothContact_measurable hu)).mpr
    (smoothContact_jacobian_integrable hu)

theorem smooth_contact_geometric_density {n : ℕ} {R a b : ℝ} {u : Point n → ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hab : a < b) (hu : ContDiff ℝ ∞ u)
    (hboundary : ∀ z ∈ abpBoundary n R a b, u z ≤ 0)
    {z0 : Point n} (hz0 : z0 ∈ abpClosed n R a b) :
    abpKappa n*(max (u z0) 0)^(2*n+1) ≤
      ∫ z in abpOpen n R a b, smoothContactDensity R a b u z := by
  have he : abpOpen n R a b ∩ smoothContact R a b u = smoothContact R a b u :=
    Set.inter_eq_right.mpr (fun _ hz => hz.1)
  rw [smoothContactDensity,setIntegral_indicator (smoothContact_measurable hu),he]
  have hgeom := smooth_contact_geometric hR hR1 hab hu hboundary hz0
  have hi : (∫ z in smoothContact R a b u, |(fderiv ℝ (contactMap u) z).det|) =
      ∫ z in smoothContact R a b u,
        timeD Set.univ u z*Matrix.det (-(hessian u z : Mat n)) := by
    apply setIntegral_congr_fun (smoothContact_measurable hu)
    exact fun z hz => contactMap_abs_det hu hz
  rwa [hi]

theorem smooth_contact_density_limit {n : ℕ} {R a b : ℝ}
    {u : ℕ → Point n → ℝ} {w M G : Point n → ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1) (hab : a < b)
    (hu : ∀ j, ContDiff ℝ ∞ (u j))
    (hboundary : ∀ j z, z ∈ abpBoundary n R a b → u j z ≤ 0)
    (hM : IntegrableOn M (abpOpen n R a b))
    (hMn : 0 ≤ᵐ[volume.restrict (abpOpen n R a b)] M)
    (hbound : ∀ j, smoothContactDensity R a b (u j) ≤ᵐ[volume.restrict (abpOpen n R a b)] M)
    (hG : IntegrableOn G (abpOpen n R a b))
    (hGn : 0 ≤ᵐ[volume.restrict (abpOpen n R a b)] G)
    (hlim : ∀ᵐ z ∂(volume.restrict (abpOpen n R a b)),
      limsup (fun j => ENNReal.ofReal (smoothContactDensity R a b (u j) z)) atTop ≤
        ENNReal.ofReal (G z))
    {z0 : Point n} (hz0 : z0 ∈ abpClosed n R a b)
    (hvalue : Tendsto (fun j => u j z0) atTop (𝓝 (w z0))) :
    abpKappa n*(max (w z0) 0)^(2*n+1) ≤ ∫ z in abpOpen n R a b, G z := by
  apply integral_reverseFatou_bound
    (fun j => smoothContactDensity_measurable (hu j))
    (fun j => Filter.Eventually.of_forall (smoothContactDensity_nonneg R a b (u j)))
    (fun j => (smoothContactDensity_integrable (hu j)).integrableOn)
    hM hMn hbound hG hGn hlim
  · exact ((hvalue.max tendsto_const_nhds).pow (2*n+1)).const_mul (abpKappa n)
  · exact fun j => smooth_contact_geometric_density hR hR1 hab (hu j) (hboundary j) hz0

end Yau.LeafProofs.L05Aux
