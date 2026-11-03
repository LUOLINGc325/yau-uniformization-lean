import Yau.LeafProofs.L18

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic

/-- A true Euclidean smooth compact cutoff equals one on an open
 neighborhood of a prescribed compact set inside an arbitrary open buffer. -/
theorem exists_euclidean_supported_smooth_cutoff
    {n : ℕ} (K O : Set (Space n)) (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ (χ : Space n → ℝ) (W : Set (Space n)),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ O ∧ IsOpen W ∧
      K ⊆ W ∧ W ⊆ O ∧ (∀ x ∈ W, χ x = 1) ∧ ∀ x, χ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨A, hAo, hKA, hAc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨B, hBo, hKB, hBA⟩ := hK.exists_isOpen_closure_subset
    ((hAo.inter hO).mem_nhdsSet.mpr (fun x hx => ⟨hKA hx, hKO hx⟩))
  have hBc : IsCompact (closure B) := hAc.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hBA hx).1)
  obtain ⟨W, hWo, hKW, hWB⟩ := hK.exists_isOpen_closure_subset (hBo.mem_nhdsSet.mpr hKB)
  obtain ⟨χ, hχs, hχr, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hBo isClosed_closure hWB
  have hsupp : tsupport χ ⊆ O := by
    change closure (Function.support χ) ⊆ O
    rw [hχsupp]
    exact fun x hx => (hBA hx).2
  have hc : HasCompactSupport χ := by
    change IsCompact (closure (Function.support χ))
    rw [hχsupp]
    exact hBc
  refine ⟨χ, W, hχs, hc, hsupp, hWo, hKW, ?_, ?_, ?_⟩
  · intro x hx
    exact (hBA (subset_closure (hWB (subset_closure hx)))).2
  · intro x hx
    exact (hχone x).mp (subset_closure hx)
  · intro x
    exact hχr (mem_range_self x)

end Yau.F04Proof
