import Mathlib

/-! The first crossing of a continuous scalar function on a closed interval. -/
noncomputable section
open Set
namespace Yau.Proofs.C04RescaledTubeAux

theorem continuous_first_crossing_Icc {F : ℝ → ℝ} {R b : ℝ} (hb : 0 ≤ b)
    (hF : Continuous F) (hzero : F 0 < R) (hone : R ≤ F b) :
    ∃ t ∈ Icc (0 : ℝ) b, F t = R ∧ ∀ u ∈ Icc (0 : ℝ) t, F u ≤ R := by
  obtain ⟨v, hv, hve⟩ := intermediate_value_Icc hb hF.continuousOn
    (show R ∈ Icc (F 0) (F b) from ⟨hzero.le, hone⟩)
  let K := Icc (0 : ℝ) b ∩ {t | F t = R}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_eq hF continuous_const)
  obtain ⟨t, ht⟩ := hK.exists_isLeast ⟨v, hv, hve⟩
  refine ⟨t, ht.1.1, ht.1.2, ?_⟩
  intro u hu
  by_contra hn
  have hRu : R < F u := lt_of_not_ge hn
  obtain ⟨v, hv, hve⟩ := intermediate_value_Icc hu.1 hF.continuousOn
    (show R ∈ Icc (F 0) (F u) from ⟨hzero.le, hRu.le⟩)
  have hvK : v ∈ K := ⟨⟨hv.1, hv.2.trans (hu.2.trans ht.1.1.2)⟩, hve⟩
  have htu : t ≤ u := (ht.2 hvK).trans hv.2
  have hut : u = t := le_antisymm hu.2 htu
  rw [hut, ht.1.2] at hRu
  exact (lt_irrefl _ hRu)

theorem continuous_first_crossing {F : ℝ → ℝ} {R : ℝ}
    (hF : Continuous F) (hzero : F 0 < R) (hone : R ≤ F 1) :
    ∃ t ∈ Icc (0 : ℝ) 1, F t = R ∧ ∀ u ∈ Icc (0 : ℝ) t, F u ≤ R :=
  continuous_first_crossing_Icc zero_le_one hF hzero hone

end Yau.Proofs.C04RescaledTubeAux
