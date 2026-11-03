import Yau.Proofs.D04ExhaustionPropagation

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

namespace Yau.Proofs.D04Aux

open Yau Yau.Blueprint

variable {n : ℕ}

theorem not_pshCollapses_of_point_anchor
    {D K : Set (ComplexVector n)} {us : ℕ → ComplexVector n → EReal}
    {φ : ℕ → ℕ} {z : ℕ → ComplexVector n} {A : ℝ}
    (hK : IsCompact K) (hKD : K ⊆ D)
    (hz : ∀ j, z j ∈ K ∧ ((-A : ℝ) : EReal) ≤ us (φ j) (z j)) :
    ¬ PshCollapses D us φ := by
  intro hcollapse
  obtain ⟨J, hJ⟩ := hcollapse K hKD hK (A + 1)
  have h := (hz J).2.trans (hJ J le_rfl (z J) (hz J).1)
  have hreal : -A ≤ -(A + 1) := EReal.coe_le_coe_iff.mp h
  linarith

theorem not_pshCollapses_of_positive_measure_anchor
    {D K : Set (ComplexVector n)} {us : ℕ → ComplexVector n → EReal}
    {φ : ℕ → ℕ} {Es : ℕ → Set (ComplexVector n)} {A c : ℝ}
    (hK : IsCompact K) (hKD : K ⊆ D) (hc : 0 < c)
    (hEs : ∀ j, Es j ⊆ K ∧ ENNReal.ofReal c ≤ lebesgueC n (Es j) ∧
      ∀ x ∈ Es j, ((-A : ℝ) : EReal) ≤ us (φ j) x) :
    ¬ PshCollapses D us φ := by
  intro hcollapse
  obtain ⟨J, hJ⟩ := hcollapse K hKD hK (A + 1)
  have hnonempty : (Es J).Nonempty := by
    by_contra hempty
    have hzero : lebesgueC n (Es J) = 0 := by rw [not_nonempty_iff_eq_empty.mp hempty]; simp
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hc)) (hzero ▸ (hEs J).2.1)
  obtain ⟨x, hx⟩ := hnonempty
  have h := ((hEs J).2.2 x hx).trans (hJ J le_rfl x ((hEs J).1 hx))
  have hreal : -A ≤ -(A + 1) := EReal.coe_le_coe_iff.mp h
  linarith

theorem coordinate_collapse_or_point_anchored_subsequence
    {D : Set (ComplexVector n)} {Ωs : ℕ → Set (ComplexVector n)}
    {us : ℕ → ComplexVector n → EReal}
    (hΩ : ∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1) ∧ Ωs j ⊆ D)
    (hcover : (⋃ j, Ωs j) = D) :
    PshCollapses D us id ∨
      ∃ (φ : ℕ → ℕ) (K : Set (ComplexVector n)) (z : ℕ → ComplexVector n) (A : ℝ),
        StrictMono φ ∧ IsCompact K ∧ K ⊆ D ∧
          ∀ j, z j ∈ K ∧ z j ∈ Ωs (φ j) ∧ ((-A : ℝ) : EReal) ≤ us (φ j) (z j) := by
  classical
  by_cases hcollapse : PshCollapses D us id
  · exact Or.inl hcollapse
  · right
    simp only [PshCollapses, id_eq] at hcollapse
    push Not at hcollapse
    obtain ⟨K, hKD, hK, A, hbad⟩ := hcollapse
    obtain ⟨N, hN⟩ := compact_eventually_subset_open_exhaustion
      (fun j => ⟨(hΩ j).1, (hΩ j).2.1⟩) hcover hK hKD
    have hf : ∃ᶠ j in atTop, ∃ x, x ∈ K ∧ x ∈ Ωs j ∧ ((-A : ℝ) : EReal) ≤ us j x := by
      rw [frequently_atTop]
      intro J
      obtain ⟨j, hj, x, hx, hxbound⟩ := hbad (max J N)
      exact ⟨j, (le_max_left J N).trans hj, x, hx,
        hN j ((le_max_right J N).trans hj) hx, hxbound.le⟩
    obtain ⟨φ, hφ, hpoints⟩ := extraction_of_frequently_atTop hf
    choose z hz using hpoints
    exact ⟨φ, K, z, A, hφ, hK, hKD, hz⟩

end Yau.Proofs.D04Aux
