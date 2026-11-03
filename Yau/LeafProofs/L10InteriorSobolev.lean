import Yau.LeafProofs.L10InteriorCommutatorBounds

/-! The successor Sobolev energy is controlled by the one-letter derivative energies. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Yau.LeafProofs

theorem sobolevNormSq_mono_order {n s t : ℕ} (O : Set (ComplexVector n))
    (u : ComplexVector n → ℂ) (hst : s ≤ t) :
    LeafCandidates.sobolevNormSq O u s ≤ LeafCandidates.sobolevNormSq O u t := by
  unfold LeafCandidates.sobolevNormSq
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun _ _ _ => integral_nonneg fun _ => sq_nonneg _)

theorem sobolevNormSq_successor_le_partials {n s : ℕ}
    {u : ComplexVector n → ℂ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O)
    (hi : ∀ k ≤ s + 1, IntegrableOn (fun x => ‖iteratedFDeriv ℝ k u x‖^2) O (lebesgueC n)) :
    LeafCandidates.sobolevNormSq O u (s + 1) ≤
      (∫ x in O, ‖u x‖^2 ∂lebesgueC n) +
        (Fintype.card (RIdx n) : ℝ) * ∑ i, LeafCandidates.sobolevNormSq O (ellipticPartial u i) s := by
  classical
  let d : ℝ := Fintype.card (RIdx n)
  have hEach (k : ℕ) (hk : k ∈ Finset.range (s + 1)) :
      (∫ x in O, ‖iteratedFDeriv ℝ (k + 1) u x‖^2 ∂lebesgueC n) ≤
        d * ∑ i, ∫ x in O, ‖iteratedFDeriv ℝ k (ellipticPartial u i) x‖^2 ∂lebesgueC n := by
    have hks : k ≤ s := by have := Finset.mem_range.mp hk; omega
    have hPart (i : RIdx n) : IntegrableOn
        (fun x => ‖iteratedFDeriv ℝ k (ellipticPartial u i) x‖^2) O (lebesgueC n) := by
      change IntegrableOn (fun x => ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ u y (realVec i)) x‖^2)
        O (lebesgueC n)
      exact elliptic_directional_jet_sq_integrableOn hO hu (hi (k + 1) (by omega)) i
    have hInt : IntegrableOn (fun x => d * ∑ i, ‖iteratedFDeriv ℝ k (ellipticPartial u i) x‖^2)
        O (lebesgueC n) := (integrable_finsetSum Finset.univ (fun i _ => hPart i)).const_mul d
    have hbound := integral_mono_ae (hi (k + 1) (by omega)) hInt
      (show ∀ᵐ x ∂(lebesgueC n).restrict O,
        ‖iteratedFDeriv ℝ (k + 1) u x‖^2 ≤ d * ∑ i, ‖iteratedFDeriv ℝ k (ellipticPartial u i) x‖^2 by
        filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
        exact elliptic_successor_jet_sq_le hO hu hx)
    simpa only [integral_const_mul, integral_finsetSum _ (fun i _ => hPart i)] using hbound
  have hTail := Finset.sum_le_sum (s := Finset.range (s + 1)) (fun k hk => hEach k hk)
  have hsum : (∑ k ∈ Finset.range (s + 1),
      d * ∑ i, ∫ x in O, ‖iteratedFDeriv ℝ k (ellipticPartial u i) x‖^2 ∂lebesgueC n) =
      d * ∑ i, LeafCandidates.sobolevNormSq O (ellipticPartial u i) s := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    rfl
  rw [hsum] at hTail
  unfold LeafCandidates.sobolevNormSq
  rw [Finset.sum_range_succ']
  simp only [norm_iteratedFDeriv_zero]
  dsimp only [d, LeafCandidates.sobolevNormSq] at hTail
  linarith

end Yau.LeafProofs
