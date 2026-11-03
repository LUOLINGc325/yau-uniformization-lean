import Yau.LeafProofs.L16CompactCoefficientBounds

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- Compact buffers bound the actual divergence drift before a solution is chosen. -/
theorem compact_buffer_drift_bound {n : ℕ} {V : Set (Space n)} (hV : IsOpen V)
    (hVc : IsCompact (closure V)) {S : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hsmooth : SmoothCoefficients (closure V ×ˢ Icc 0 S) a b) :
    ∃ D : ℝ, 0 < D ∧ ∀ p ∈ V ×ˢ Ioo 0 S, ∑ j, (energyDrift a b p j) ^ 2 ≤ D ^ 2 := by
  classical
  let K : Set (Point n) := closure V ×ˢ Icc 0 S
  let U : Set (Point n) := V ×ˢ Ioo 0 S
  have hK : IsCompact K := hVc.prod isCompact_Icc
  have hU : IsOpen U := hV.prod isOpen_Ioo
  have hUK : U ⊆ K := fun p hp => ⟨subset_closure hp.1, Ioo_subset_Icc_self hp.2⟩
  obtain ⟨L, hL, hDeriv⟩ := bounded_fderiv_on_open_subset_of_compact hK hU hUK
    (hsmooth.1.of_le (by simp))
  have hEachB (j : Yau.RIdx n) : ∃ C : ℝ, ∀ p ∈ K, |b p j| ≤ C := by
    simpa only [Real.norm_eq_abs] using hK.exists_bound_of_continuousOn (hsmooth.2 j).continuousOn
  choose C hC using hEachB
  let B : ℝ := 1 + ∑ j, |C j|
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBoundB : ∀ p ∈ U, ∀ j, |b p j| ≤ B := by
    intro p hp j
    have hCj : |C j| ≤ ∑ k, |C k| :=
      Finset.single_le_sum (fun k _ => abs_nonneg (C k)) (Finset.mem_univ j)
    exact (hC j p (hUK hp)).trans (by dsimp only [B]; linarith [le_abs_self (C j)])
  have hSpatial : ∀ p ∈ U, ∀ i j, |d (fun x => a (x, p.2) i j) p.1 i| ≤ L := by
    intro p hp i j
    have ha : DifferentiableAt ℝ a p :=
      ((hsmooth.1.mono hUK).contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
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
      _ ≤ |b p j| + |∑ i, d (fun x => a (x, p.2) i j) p.1 i| := abs_sub _ _
      _ ≤ B + ∑ _i : Yau.RIdx n, L := add_le_add (hBoundB p hp j)
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hSpatial p hp i j)))
  let D : ℝ := 1 + ∑ _j : Yau.RIdx n, M
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro p hp
  have hSum : ∑ j, |energyDrift a b p j| ≤ D := by
    exact (Finset.sum_le_sum (fun j _ => hDrift p hp j)).trans
      (by dsimp only [D]; linarith)
  simpa only [sq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => abs_nonneg (energyDrift a b p j))).trans
      ((sq_le_sq₀ (Finset.sum_nonneg (fun j _ => abs_nonneg (energyDrift a b p j))) hD.le).mpr hSum)

end Yau.F04Proof
