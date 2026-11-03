import Yau.Proofs.C04ClockOrder
import Yau.Proofs.C04RicciNormalization

/-! The original good windows turn the smaller-clock Ricci estimate into a
uniform lower bound for the same scalar-normalized central metrics. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter Set

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem center_lower_of_good_window (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {a b K T : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hK : 0 < K)
    (hmin : ∀ t u, T ≤ t → 0 ≤ u → ρ o u = a * ρ o t →
      b * clockSpeed o h u ≤ ricciMin o h t) :
    ∃ B, 0 < B ∧ ∀ S t, B ≤ S → 0 < t → T ≤ t →
      5 * S / 4 ≤ ρ o t → ρ o t ≤ 7 * S / 4 →
      (∀ v u, 0 ≤ v → 0 ≤ u → ρ o v = 2 * S → ρ o u = a * S →
        clockSpeed o h v ≤ K * clockSpeed o h u) →
      ∀ hR : 0 < scalarCurvature (h t) o,
        b / K ≤ relMinEigenvalue
          (gMat (scaleField (scalarCurvature (h t) o) hR (h t)) o)
          (ricci (scaleField (scalarCurvature (h t) o) hR (h t)) o) := by
  obtain ⟨A, hAone, hsA, time, htime, hinv, hmono, hinf⟩ := clock_inverse X o h U P ρ hf hH
  let B := max 1 (ρ o A / a)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨B, hB, ?_⟩
  intro S t hSB ht htT hleft hright hwindow hR
  have hS : 0 < S := hB.trans_le hSB
  have hAS : ρ o A ≤ a * S := by
    have hh : ρ o A / a ≤ S := (le_max_right _ _).trans hSB
    exact (div_le_iff₀ ha).mp hh |>.trans_eq (mul_comm _ _)
  have hSt : S ≤ ρ o t := by linarith
  have hAt : ρ o A ≤ a * ρ o t := hAS.trans (mul_le_mul_of_nonneg_left hSt ha.le)
  have hA2S : ρ o A ≤ 2 * S := by
    exact hAS.trans (mul_le_mul_of_nonneg_right (by linarith : a ≤ 2) hS.le)
  obtain ⟨huA, hueq⟩ := htime (a * ρ o t) hAt
  obtain ⟨hvA, hveq⟩ := htime (a * S) hAS
  obtain ⟨hwA, hweq⟩ := htime (2 * S) hA2S
  have hu0 : 0 ≤ time (a * ρ o t) := zero_le_one.trans (hAone.trans huA)
  have hvpos : 0 < time (a * S) := zero_lt_one.trans_le (hAone.trans hvA)
  have hw0 : 0 ≤ time (2 * S) := zero_le_one.trans (hAone.trans hwA)
  have hcompare : clockSpeed o h t ≤ K * clockSpeed o h (time (a * ρ o t)) := by
    calc
      clockSpeed o h t ≤ clockSpeed o h (time (2 * S)) :=
        clockSpeed_le_of_clock_le X o h U P ρ hf hH ht hw0 (by rw [hweq]; linarith)
      _ ≤ K * clockSpeed o h (time (a * S)) :=
        hwindow _ _ hw0 hvpos.le hweq hveq
      _ ≤ K * clockSpeed o h (time (a * ρ o t)) := by
        apply mul_le_mul_of_nonneg_left _ hK.le
        apply clockSpeed_le_of_clock_le X o h U P ρ hf hH hvpos hu0
        rw [hveq, hueq]
        exact mul_le_mul_of_nonneg_left hSt ha.le
  exact normalized_lower_of_clock_comparison X o h t (time (a * ρ o t)) b K
    ht hb hK hR hcompare (hmin t _ htT hu0 hueq)

end Yau.Proofs.C04Aux
