import Yau.LeafProofs.L16ExpBoundaryBounds

/-! Entrywise coefficient and source bounds on the fixed coordinate compact. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_compact_coefficient_source_bounds {K : Set (Point n)} (hK : IsCompact K)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {R : Point n → ℝ}
    (hab : SmoothCoefficients K a b) (hR : ContDiffOn ℝ ∞ R K) :
    ∃ A₀ b₀ R₀ : ℝ, 0 < A₀ ∧ 0 < b₀ ∧ 0 < R₀ ∧
      (∀ z ∈ K, ∀ i j, |a z i j| ≤ A₀) ∧
      (∀ z ∈ K, ∀ i, |b z i| ≤ b₀) ∧ ∀ z ∈ K, |R z| ≤ R₀ := by
  classical
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn hab.1.continuousOn
  have hEach (i : Yau.RIdx n) : ∃ C : ℝ, ∀ z ∈ K, |b z i| ≤ C := by
    simpa only [Real.norm_eq_abs] using hK.exists_bound_of_continuousOn (hab.2 i).continuousOn
  choose C hC using hEach
  obtain ⟨F,hF⟩ := hK.exists_bound_of_continuousOn hR.continuousOn
  refine ⟨1+|A|,1+∑ i, |C i|,1+|F|,by positivity,by positivity,by positivity,?_,?_,?_⟩
  · intro z hz i j
    exact (frobenius_entry_abs_le _ i j).trans
      ((hA z hz).trans (by linarith [le_abs_self A]))
  · intro z hz i
    have hi : |C i| ≤ ∑ j, |C j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)
    exact (hC i z hz).trans (by linarith [le_abs_self (C i)])
  · intro z hz
    have hh : |R z| ≤ F := by simpa only [Real.norm_eq_abs] using hF z hz
    exact hh.trans (by linarith [le_abs_self F])

end Yau.Proofs.F05Aux
