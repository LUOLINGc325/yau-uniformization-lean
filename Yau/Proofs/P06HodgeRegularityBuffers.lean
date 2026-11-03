import Yau.LeafProofs.L03RawChartForms

/-! Data-independent compact buffers and smooth plateaux in an arbitrary
finite-dimensional real coordinate space. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem regularity_exists_compact_cutoff {O K : Set E}
    (hO : IsOpen O) (hcK : IsCompact K) (hKO : K ⊆ O) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧
      (∀ z, χ z ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ z ∈ K, χ z = 1) := by
  obtain ⟨B, hB, hKB, hBO, hcB⟩ := exists_open_between_and_isCompact_closure hcK hO hKO
  obtain ⟨χ, hχ, hχrange, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hB hcK.isClosed hKB
  refine ⟨χ,hχ,?_,?_,fun z => hχrange (Set.mem_range_self z),fun z hz => (hχone z).mp hz⟩
  · change IsCompact (tsupport χ)
    simpa only [tsupport,hχsupport] using hcB
  · simpa only [tsupport,hχsupport] using hBO

end Yau.NodeProofs.P06Aux
