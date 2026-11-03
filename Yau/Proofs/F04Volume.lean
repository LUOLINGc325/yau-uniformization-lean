import Yau.Proofs.F04Source
import spec.CHAIN.FlowMassObligations

/-! Bind the proved localized-flow density identities and the initial
Riemannian-volume facts to the existing registered mass predicates. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem massVolumeTransport (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) : FlowMass.MassVolumeTransport X h P ρ := by
  intro T hT
  refine ⟨?_, ?_, ?_⟩
  · intro c
    exact ((hloc.2.2.2.1 c).neg.exp).mono (by
      intro p hp
      exact ⟨hp.1, hp.2.1⟩)
  · intro x t ht
    refine ⟨density_pos ρ x t, density_le_one o h U P ρ hloc x t ht.1, ?_,
      density_eq_det_ratio o h U P ρ hloc x t ht.1, ?_⟩
    · dsimp [FlowMass.flowMassDensity]
      rw [(hloc.2.2.2.2.2.2.2.2.2.1 x t ht.1).1, neg_neg]
    · exact (density_hasDerivWithinAt o h U P ρ hloc x t ht.1).mono (fun _ hs => hs.1)
  · intro μg hμg t ht μt hμt
    exact volume_density_transport o h U P ρ hloc t ht.1 μg μt hμg hμt

theorem riemannianVolumeLocality (X : KahlerManifold n) :
    FlowMass.RiemannianVolumeLocality X := by
  intro μ hμ
  let _ : IsLocallyFiniteMeasure μ :=
    LeafProofs.L18Aux.riemannianVolume_locallyFinite X.metric μ hμ
  refine ⟨fun K hK => hK.measure_lt_top, ?_⟩
  intro O hO hO'
  exact LeafProofs.L18Aux.riemannianVolume_open_pos X.metric μ hμ hO hO'

end Yau.F04Proof
