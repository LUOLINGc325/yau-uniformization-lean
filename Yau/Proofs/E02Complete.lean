import Yau.Proofs.E02FixedListProducer
import Yau.Proofs.E02SmallWeightLimit
import Yau.Proofs.E02OriginalContraction
import Yau.Proofs.E02DimensionZero
import spec.CHAIN.CONTRACTS

open Matrix Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The ORIGINAL ellipsoid comparison, on the same flow and chart.
The original maximizing B is chosen before every contact-weight list. -/
theorem ellipsoidComparison_of_original_ancestors {n : ℕ}
    (X : KahlerManifold n) (h : Flow X) (ρ : STF X)
    (hh : MetricFamilySmooth h (Ici 0)) (hoc : OptimizerContacts X h ρ)
    (hV01 : EnvelopeInequality X h) : EllipsoidComparison X h := by
  intro T hT x z t hz ht f hf hValue hLower
  obtain ⟨B,hB,hMax,_hLog,hContacts⟩ :=
    optimizerContacts_one_matrix X h ρ hoc hT x z t hz ht
  have hMajorant : ∃ K : Herm n, K.PosSemidef ∧
      (K-leviC (fun w => f (w,t)) z).PosSemidef ∧
      tracePair B K ≤ deriv (fun s => f (z,s)) t := by
    apply exists_psd_majorant_from_small_weights B (leviC (fun w => f (w,t)) z)
      hB.1 (deriv (fun s => f (z,s)) t)
    intro δ hδ hδHalf
    obtain ⟨m,η,α,hEach,hGram,hSum⟩ := hContacts δ hδ
    have hα : ∀ i, 0 < α i := fun i => (hEach i).1
    have hWeight : ∀ i, α i ≤ δ := fun i => (hEach i).2.1
    have hEnv : ∀ i, envelopeChart h T x (z,η i,t) = 1 := fun i => (hEach i).2.2.1
    have hq : ∀ i, qform B (η i) = 1 := fun i => (hEach i).2.2.2
    have hColumns : weightedColumns α η*(weightedColumns α η)ᴴ = B⁻¹ :=
      (weightedColumns_gram α η (fun i => (hα i).le)).trans hGram
    have hδOne : δ < 1 := hδHalf.trans (by norm_num)
    obtain ⟨K,hK,hDom,hTrace⟩ := fixed_list_original_majorant X h ρ hh hoc hV01 T hT x (z,t)
      hz ht B hB hMax α hα η hColumns hEnv hq hSum f hf hValue hLower δ δ hδ hδOne hδOne hWeight
    exact ⟨K,hK,hDom,by simpa only [pow_two] using hTrace⟩
  obtain ⟨K,hK,hDom,hTrace⟩ := hMajorant
  exact optimizer_majorant_original_contraction X h T x z t hz ht B hB hMax
    K (leviC (fun w => f (w,t)) z) (deriv (fun s => f (z,s)) t) hK hDom hTrace

end Yau.NodeProofs.E02Aux

namespace Yau.NodeProofs
open Yau Yau.Blueprint Yau.BlueprintContracts

/-- Exact registered ancestors only; the original universal E02 target,
including n=0 and the same arbitrary LocalizedFlow witness, is retained. -/
theorem E02_of_E01_V01 (hE01 : E01_contract) (hV01 : V01_contract) : E02_contract := by
  intro n X o h U P ρ hloc
  exact E02Aux.ellipsoidComparison_of_original_ancestors X h ρ hloc.1.2.1
    (hE01 n X o h U P ρ hloc) (hV01 n X o h U P ρ hloc)

end Yau.NodeProofs
