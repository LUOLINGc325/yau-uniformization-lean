import Yau.Proofs.F04EnergyCoreTests

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L12Aux Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- A genuine smooth compact cutoff inside an arbitrary open set, equal to
one on an open neighborhood of the prescribed compact subset. -/
theorem exists_supported_smooth_cutoff (K O : Set M.Carrier)
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ (η : M.Carrier → ℝ) (W : Set M.Carrier),
      SmoothFn η ∧ HasCompactSupport η ∧ tsupport η ⊆ O ∧ IsOpen W ∧
      K ⊆ W ∧ W ⊆ O ∧ (∀ x ∈ W, η x = 1) ∧ ∀ x, η x ∈ Icc (0 : ℝ) 1 := by
  let := manifold_realSmooth M
  let : LocallyCompactSpace M.Carrier := manifold_locallyCompact M
  obtain ⟨A, hAo, hKA, hAc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨B, hBo, hKB, hBA⟩ := hK.exists_isOpen_closure_subset
    ((hAo.inter hO).mem_nhdsSet.mpr (fun x hx => ⟨hKA hx, hKO hx⟩))
  have hBc : IsCompact (closure B) := hAc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hBA hx).1)
  obtain ⟨W, hWo, hKW, hWB⟩ := hK.exists_isOpen_closure_subset (hBo.mem_nhdsSet.mpr hKB)
  obtain ⟨η, hηs, hηr, hηsupp, hηone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, ComplexVector n)) (n := (⊤ : ℕ∞))
      hBo isClosed_closure hWB
  have hsupp : tsupport η ⊆ O := by
    change closure (Function.support η) ⊆ O
    rw [hηsupp]
    exact fun x hx => (hBA hx).2
  have hc : HasCompactSupport η := by
    change IsCompact (closure (Function.support η))
    rw [hηsupp]
    exact hBc
  refine ⟨η, W, Yau.LeafProofs.L18Aux.smoothFn_of_contMDiff_real hηs, hc, hsupp,
    hWo, hKW, ?_, ?_, ?_⟩
  · intro x hx
    exact (hBA (subset_closure (hWB (subset_closure hx)))).2
  · intro x hx
    exact (hηone x).mp (subset_closure hx)
  · intro x
    exact hηr (mem_range_self x)

end Yau.F04Proof
