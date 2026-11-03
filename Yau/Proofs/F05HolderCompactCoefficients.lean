import Yau.LeafProofs.L16CompactCoefficientBounds

/-! The actual energy drift is bounded using fixed coefficients on a general
compact set and an open subset. No smooth-boundary or candidate hypothesis. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_compact_coefficient_bounds {K U : Set (Point n)}
    (hK : IsCompact K) (hU : IsOpen U) (hUK : U ⊆ K)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    (hSmooth : SmoothCoefficients K a b) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      (∀ p ∈ K, ∀ i j, |a p i j| ≤ A) ∧
      ∀ p ∈ U, ∑ j, |energyDrift a b p j|^2 ≤ D^2 := by
  classical
  obtain ⟨A₀,hA₀⟩ := hK.exists_bound_of_continuousOn hSmooth.1.continuousOn
  obtain ⟨L,hL,hDeriv⟩ := bounded_fderiv_on_open_subset_of_compact hK hU hUK
    (hSmooth.1.of_le (by simp))
  have hEachB (j : Yau.RIdx n) : ∃ C : ℝ, ∀ p ∈ K, |b p j| ≤ C := by
    simpa only [Real.norm_eq_abs] using
      hK.exists_bound_of_continuousOn (hSmooth.2 j).continuousOn
  choose C hC using hEachB
  let B : ℝ := 1 + ∑ j, |C j|
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBoundB : ∀ p ∈ U, ∀ j, |b p j| ≤ B := by
    intro p hp j
    have hCj : |C j| ≤ ∑ k, |C k| := Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ j)
    exact (hC j p (hUK hp)).trans (by dsimp only [B]; linarith [le_abs_self (C j)])
  have hSpatial : ∀ p ∈ U, ∀ i j,
      |d (fun x => a (x,p.2) i j) p.1 i| ≤ L := by
    intro p hp i j
    have ha : DifferentiableAt ℝ a p :=
      ((hSmooth.1.mono hUK).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
    rw [coefficient_spatial_derivative_eq_joint ha]
    have hNorm : ‖(Yau.realVec i, (0 : ℝ))‖ = 1 := by
      simp only [Prod.norm_def, realVec_norm, norm_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
    exact (frobenius_entry_abs_le _ i j).trans
      (((fderiv ℝ a p).le_opNorm _).trans (by rw [hNorm, mul_one]; exact hDeriv p hp))
  let M : ℝ := B + ∑ _i : Yau.RIdx n, L
  have hM : 0 < M := by
    dsimp only [M]
    exact add_pos_of_pos_of_nonneg hB (Finset.sum_nonneg (fun _ _ => hL.le))
  have hDrift : ∀ p ∈ U, ∀ j, |energyDrift a b p j| ≤ M := by
    intro p hp j
    calc
      |energyDrift a b p j| ≤ |b p j| + |∑ i, d (fun x => a (x,p.2) i j) p.1 i| := abs_sub _ _
      _ ≤ B + ∑ _i : Yau.RIdx n, L := add_le_add (hBoundB p hp j)
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hSpatial p hp i j)))
  let D : ℝ := 1 + ∑ _j : Yau.RIdx n, M
  have hD : 0 < D := by
    dsimp only [D]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun _ _ => hM.le))
  refine ⟨1+|A₀|, D, by positivity, hD, ?_, ?_⟩
  · intro p hp i j
    exact (frobenius_entry_abs_le _ i j).trans
      ((hA₀ p hp).trans (by linarith [le_abs_self A₀]))
  · intro p hp
    have hSum : ∑ j, |energyDrift a b p j| ≤ D := by
      exact (Finset.sum_le_sum (fun j _ => hDrift p hp j)).trans
        (by dsimp only [D]; linarith)
    exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg (energyDrift a b p j))).trans
      (sq_le_sq₀ (Finset.sum_nonneg (fun j _ => abs_nonneg (energyDrift a b p j))) hD.le |>.mpr hSum)


end Yau.Proofs.F05Aux
