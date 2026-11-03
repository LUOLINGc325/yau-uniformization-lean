import Yau.Proofs.F04FlowTraceBound
import Yau.Proofs.F03TraceOrder

/-! The actual given flow admits the compact closed-slab Loewner comparison needed for the cutoff remainder. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder
namespace Yau.Proofs.F03Aux
open Yau Blueprint
variable {n : ℕ}

theorem flow_compact_hermLE
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ C : ℝ,0 < C ∧ ∀ x ∈ K,∀ t ∈ Icc 0 T,
      HermLE (gMat X.metric.form x) ((C:ℂ) • gMat (h t) x) := by
  obtain ⟨C,hC,hTrace⟩ := F04Proof.flow_compact_trace_bound X o h U P ρ hf hT K hK
  refine ⟨C,hC,fun x hx t ht => ?_⟩
  exact posSemidef_le_relative_trace_bound (gMat (h t) x) (gMat X.metric.form x)
    (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x))
    (LeafProofs.L18Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef
    hC.le (hTrace x hx t ht)

end Yau.Proofs.F03Aux
