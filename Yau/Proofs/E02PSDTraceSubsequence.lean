import Yau.Proofs.E02PSDTraceCompact

open Matrix Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_psd_trace_subsequence {n : ℕ} (Kseq : ℕ → Herm n) (R : ℝ)
    (hK : ∀ j, (Kseq j).PosSemidef) (hBound : ∀ j, (Matrix.trace (Kseq j)).re ≤ R) :
    ∃ K : Herm n, K.PosSemidef ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (Kseq ∘ φ) atTop (𝓝 K) := by
  haveI : FirstCountableTopology (Herm n) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  have hCone : ∀ j, Kseq j ∈ psdTraceCone n R := fun j => ⟨hK j,hBound j⟩
  obtain ⟨K,hKC,φ,hφ,hKL⟩ := (isCompact_psdTraceCone n R).tendsto_subseq hCone
  exact ⟨K,hKC.1,φ,hφ,hKL⟩

end Yau.NodeProofs.E02Aux
