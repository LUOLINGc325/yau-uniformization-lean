import Yau.Proofs.F04Adjoint

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem flow_density_integral {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (μg μt : Measure (Pt X))
    (hμg : IsRiemannianVolume X.metric.form μg) (hμt : IsRiemannianVolume (h t) μt)
    (f : Pt X → ℝ) :
    (∫ x, f x ∂μt) = ∫ x, density ρ x t * f x ∂μg := by
  have hd : SmoothFn (fun x => density ρ x t) := by
    intro c
    exact ((hloc.2.2.2.1 c).neg.exp).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun _ hz => ⟨hz, ht⟩)
  have hm : Measurable (fun x => ENNReal.ofReal (density ρ x t)) :=
    ENNReal.measurable_ofReal.comp (LeafProofs.L18Aux.continuous_of_smoothFn hd).measurable
  rw [volume_density_transport o h U P ρ hloc t ht μg μt hμg hμt]
  simpa only [ENNReal.toReal_ofReal (density_pos ρ _ _).le, smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) f

theorem flow_density_compact_adjoint {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (μg μt : Measure (Pt X))
    (hμg : IsRiemannianVolume X.metric.form μg) (hμt : IsRiemannianVolume (h t) μt)
    (v ψ : Pt X → ℝ) (hv : SmoothFn v) (hψ : SmoothFn ψ) (hcψ : HasCompactSupport ψ) :
    (∫ x, (ψ x * laplacian (h t) v x) * density ρ x t ∂μg) =
      ∫ x, (v x * laplacian (h t) ψ x) * density ρ x t ∂μg := by
  have hh := compactKahlerAdjoint o h U P ρ hloc t ht μt hμt v ψ hv hψ hcψ
  rw [flow_density_integral X o h U P ρ hloc ht μg μt hμg hμt,
    flow_density_integral X o h U P ρ hloc ht μg μt hμg hμt] at hh
  simpa only [mul_comm] using hh

end Yau.F04Proof
