import Yau.Proofs.F04C1TimeDerivative
import Yau.Proofs.F04CompactIntegral
import Yau.Proofs.F04Volume

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem c1_compact_mass_differentiation {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {S : ℝ} {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceC1Time v (Icc 0 S))
    {K : Set M.Carrier} (hK : IsCompact K)
    (hsupp : ∀ x t, t ∈ Icc 0 S → x ∉ K → v x t = 0) :
    ContinuousOn (fun t => ∫ x, v x t ∂μ) (Icc 0 S) ∧
      ∀ t ∈ Ioo 0 S, Integrable (fun x => v x t) μ ∧
        Integrable (fun x => deriv (v x) t) μ ∧
        HasDerivAt (fun s => ∫ x, v x s ∂μ) (∫ x, deriv (v x) t ∂μ) t := by
  let : IsLocallyFiniteMeasure μ := LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  refine ⟨compact_integral_continuousOn hK (smoothSpaceC1Time_continuousOn hv) hsupp, ?_⟩
  have hvo : SmoothSpaceC1Time v (Ioo 0 S) :=
    ⟨fun t ht => hv.1 t (Ioo_subset_Icc_self ht),
      fun x => (hv.2 x).mono (Set.prod_mono (Subset.refl _) Ioo_subset_Icc_self)⟩
  have hd : ∀ x t, t ∈ Ioo 0 S → x ∉ K → deriv (v x) t = 0 := by
    intro x t ht hx
    have he : v x =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hsupp x s (Ioo_subset_Icc_self hs) hx
    simpa only [deriv_const] using he.deriv_eq
  intro t ht
  exact compact_integral_hasDerivAt isOpen_Ioo hK
    (smoothSpaceC1Time_continuousOn hvo)
    (smoothSpaceC1Time_timeDerivative_continuousOn isOpen_Ioo hvo)
    (fun x s hs hx => hsupp x s (Ioo_subset_Icc_self hs) hx) hd
    (fun x s hs => smoothSpaceC1Time_hasDerivAt isOpen_Ioo hvo x hs) ht

end Yau.F04Proof
