import Yau.Proofs.F04FlowMassDerivative

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- Closed-time continuity plus genuine open-time C1 regularity suffices
 for differentiation of a compact mass. No initial derivative is assumed. -/
theorem openTime_compact_mass_differentiation
    {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {S : ℝ} {v : M.Carrier → ℝ → ℝ}
    (hvC : ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (univ ×ˢ Icc 0 S))
    (hv : SmoothSpaceC1Time v (Ioo 0 S)) {K : Set M.Carrier} (hK : IsCompact K)
    (hsupp : ∀ x t, t ∈ Icc 0 S → x ∉ K → v x t = 0) :
    ContinuousOn (fun t => ∫ x, v x t ∂μ) (Icc 0 S) ∧
      ∀ t ∈ Ioo 0 S, Integrable (fun x => v x t) μ ∧
        Integrable (fun x => deriv (v x) t) μ ∧
        HasDerivAt (fun s => ∫ x, v x s ∂μ) (∫ x, deriv (v x) t ∂μ) t := by
  let : IsLocallyFiniteMeasure μ := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  refine ⟨compact_integral_continuousOn hK hvC hsupp,?_⟩
  have hd : ∀ x t, t ∈ Ioo 0 S → x ∉ K → deriv (v x) t = 0 := by
    intro x t ht hx
    have he : v x =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hsupp x s (Ioo_subset_Icc_self hs) hx
    simpa only [deriv_const] using he.deriv_eq
  intro t ht
  exact compact_integral_hasDerivAt isOpen_Ioo hK (smoothSpaceC1Time_continuousOn hv)
    (smoothSpaceC1Time_timeDerivative_continuousOn isOpen_Ioo hv)
    (fun x s hs hx => hsupp x s (Ioo_subset_Icc_self hs) hx) hd
    (fun x s hs => smoothSpaceC1Time_hasDerivAt isOpen_Ioo hv x hs) ht

/-- A fixed compact spatial cutoff preserves the true mass derivative
 when only the initial continuous trace is available. -/
theorem cutoff_mass_differentiation_openTime
    {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {S : ℝ} {v : M.Carrier → ℝ → ℝ}
    (hvC : ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (univ ×ˢ Icc 0 S))
    (hv : SmoothSpaceC1Time v (Ioo 0 S))
    {φ : M.Carrier → ℝ} (hφ : SmoothFn φ) (hcφ : HasCompactSupport φ) :
    ContinuousOn (fun t => ∫ x, φ x*v x t ∂μ) (Icc 0 S) ∧
      ∀ t ∈ Ioo 0 S,
        HasDerivAt (fun s => ∫ x, φ x*v x s ∂μ) (∫ x, φ x*deriv (v x) t ∂μ) t := by
  have hφC : Continuous (fun p : M.Carrier × ℝ => φ p.1) :=
    (Yau.LeafProofs.L18Aux.continuous_of_smoothFn hφ).comp continuous_fst
  have hprod := smoothSpaceC1Time_mul (smoothSpaceC1Time_spatial_const hφ) hv
  have hsupp : ∀ x t, t ∈ Icc 0 S → x ∉ tsupport φ → φ x*v x t = 0 := by
    intro x t _ht hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hh := openTime_compact_mass_differentiation g μ hμ (hφC.continuousOn.mul hvC) hprod hcφ hsupp
  refine ⟨hh.1,?_⟩
  intro t ht
  have heq : (∫ x, deriv (fun s => φ x*v x s) t ∂μ) = ∫ x, φ x*deriv (v x) t ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun x => ((smoothSpaceC1Time_hasDerivAt isOpen_Ioo hv x ht).const_mul (φ x)).deriv)
  rw [← heq]
  exact (hh.2 t ht).2.2

end Yau.F04Proof
