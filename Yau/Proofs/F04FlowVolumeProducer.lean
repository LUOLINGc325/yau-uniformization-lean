import Yau.Proofs.F04ReferenceVolume

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold ENNReal

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ}

/-- The actual localized flow produces its evolving volume from the given
initial volume, without completeness of h_t or a volume-existence premise. -/
theorem flow_reference_volume
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (t : ℝ) (ht : 0 ≤ t) :
    IsRiemannianVolume (h t) (μ.withDensity (fun x => ENNReal.ofReal (density ρ x t))) := by
  have hv := isRiemannianVolume_from_reference X.metric (h t)
    (metricFamilySmooth_slice h (Ici 0) hloc.1.2.1 t ht) μ hμ
  have he : μ.withDensity (fun x => ENNReal.ofReal (Yau.LeafProofs.metricDensityRatio (h t) X.metric.form x)) =
      μ.withDensity (fun x => ENNReal.ofReal (density ρ x t)) := by
    congr 1
    funext x
    apply congrArg ENNReal.ofReal
    exact (density_eq_det_ratio o h U P ρ hloc x t ht).symm
  rw [he] at hv
  exact hv

end Yau.F04Proof
