import Yau.Proofs.G04RicciForm
import Yau.Proofs.G04KahlerForm

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem kahlerLeviForms (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h) :
    PaperKahlerLeviFormNormalization h := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨omegaForm h, omegaForm_smooth h hs, omegaForm_oneOne h,
      omegaForm_closed h hs hk, omegaForm_represents h, fun x z _ I => omegaForm_components h x z I⟩
  · intro f hf
    obtain ⟨hsmooth, h11, hc, hrep⟩ := dd_properties f hf
    exact ⟨ddRealForm f, hsmooth, h11, hc, hrep, fun x z hz I => dd_coefficients f hf x hz I⟩
  · exact ⟨rhoForm h hs, rhoForm_smooth h hs,
      iotaRealForm_oneOne (ricci h) (ricci_hermitian h hs), rhoForm_closed h hs,
      iotaRealForm_represents (ricci h) (ricci_hermitian h hs),
      fun x z hz I => rhoForm_components h hs x hz I⟩

end Yau.NodeProofs.G04Aux
