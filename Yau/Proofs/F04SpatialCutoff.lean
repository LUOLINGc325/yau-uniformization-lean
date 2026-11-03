import Yau.Proofs.F04CoefficientBounds
import Yau.Proofs.F04FullGradientEnergy

open MeasureTheory Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem spatial_energy_cutoff {n : ℕ} {V₀ V₁ : Set (Space n)}
    (hV₀c : IsCompact (closure V₀)) (hV₁ : IsOpen V₁) (hV₀V₁ : closure V₀ ⊆ V₁) :
    ∃ (η : Space n → ℝ) (M : ℝ), ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ V₁ ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x ∈ closure V₀, η x = 1) ∧ 0 ≤ M ∧
      ∀ x, (∑ i, (d η x i) ^ 2) + (η x) ^ 2 ≤ M := by
  obtain ⟨W, hW, hVW, hWV, hWc⟩ :=
    exists_open_between_and_isCompact_closure hV₀c hV₁ hV₀V₁
  obtain ⟨η, hη, hηrange, hηsupport, hηone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW isClosed_closure hVW
  have hηts : tsupport η = closure W := by rw [tsupport, hηsupport]
  have hcη : HasCompactSupport η := by simpa only [HasCompactSupport, hηts] using hWc
  obtain ⟨L, hL⟩ := hη.lipschitzWith_of_hasCompactSupport hcη (by simp)
  let M : ℝ := 1 + ∑ _i : Yau.RIdx n, (L : ℝ) ^ 2
  refine ⟨η, M, hη, hcη, hηts ▸ hWV, ?_, ?_, by dsimp only [M]; positivity, ?_⟩
  · exact fun x => hηrange (mem_range_self x)
  · exact fun x hx => (hηone x).mp hx
  intro x
  have hder (i : Yau.RIdx n) : |d η x i| ≤ (L : ℝ) := by
    change ‖fderiv ℝ η x (Yau.realVec i)‖ ≤ (L : ℝ)
    exact ((fderiv ℝ η x).le_opNorm _).trans
      (by rw [realVec_norm, mul_one]; exact norm_fderiv_le_of_lipschitz ℝ hL)
  have hsum : (∑ i, (d η x i) ^ 2) ≤ ∑ _i : Yau.RIdx n, (L : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hder i) 2
  have hηx := hηrange (mem_range_self x)
  have hsquare : (η x) ^ 2 ≤ 1 := by nlinarith [hηx.1, hηx.2, sq_nonneg (η x)]
  dsimp only [M]
  linarith only [hsum, hsquare]

theorem timeConstant_spatial_cutoff {n : ℕ} {O : Set (Space n)} {η : Space n → ℝ}
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hηO : tsupport η ⊆ O)
    (hηrange : ∀ x, 0 ≤ η x ∧ η x ≤ 1) (a b : ℝ) :
    DGSpatialCutoff O a b (fun p : Point n => η p.1) := by
  refine ⟨hη.comp contDiff_fst, (fun p _ => hηrange p.1), tsupport η, hcη, hηO, ?_⟩
  intro p _ hp
  exact image_eq_zero_of_notMem_tsupport hp

end Yau.F04Proof
