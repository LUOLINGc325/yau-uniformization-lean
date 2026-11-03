import Mathlib

/-! An actual compact path contained in an open set has a slightly enlarged
time interval contained in that same open set. -/

noncomputable section
open Filter Set
open scoped Topology

namespace Yau.Proofs.C03Aux

theorem exists_curve_interval_neighborhood {E : Type*} [TopologicalSpace E]
    (γ : ℝ → E) (δ : ℝ) (hδ : 0 < δ)
    (hγ : ContinuousOn γ (Ioo (-δ) (1 + δ))) (O : Set E) (hO : IsOpen O)
    (himage : MapsTo γ (Icc (0 : ℝ) 1) O) :
    ∃ η : ℝ, 0 < η ∧ Ioo (-η) (1 + η) ⊆ Ioo (-δ) (1 + δ) ∧
      MapsTo γ (Ioo (-η) (1 + η)) O := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) (1 + δ) := by constructor <;> linarith
  have h1 : (1 : ℝ) ∈ Ioo (-δ) (1 + δ) := by constructor <;> linarith
  have H0 := (hγ.continuousAt (isOpen_Ioo.mem_nhds h0)).preimage_mem_nhds
    (hO.mem_nhds (himage (show (0 : ℝ) ∈ Icc 0 1 by norm_num)))
  have H1 := (hγ.continuousAt (isOpen_Ioo.mem_nhds h1)).preimage_mem_nhds
    (hO.mem_nhds (himage (show (1 : ℝ) ∈ Icc 0 1 by norm_num)))
  obtain ⟨ε0, hε0, hb0⟩ := Metric.mem_nhds_iff.mp H0
  obtain ⟨ε1, hε1, hb1⟩ := Metric.mem_nhds_iff.mp H1
  let η := min δ (min ε0 ε1) / 2
  have hη : 0 < η := div_pos (lt_min hδ (lt_min hε0 hε1)) (by norm_num)
  have hηδ : η ≤ δ / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hη0 : η ≤ ε0 / 2 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hη1 : η ≤ ε1 / 2 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  refine ⟨η, hη, ?_, ?_⟩
  · intro t ht
    constructor <;> linarith [ht.1, ht.2]
  · intro t ht
    by_cases ht0 : t < 0
    · apply hb0
      change dist t 0 < ε0
      rw [Real.dist_eq, sub_zero, abs_of_neg ht0]
      linarith [ht.1]
    · by_cases ht1 : 1 < t
      · apply hb1
        change dist t 1 < ε1
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht1)]
        linarith [ht.2]
      · exact himage ⟨le_of_not_gt ht0, le_of_not_gt ht1⟩

end Yau.Proofs.C03Aux
