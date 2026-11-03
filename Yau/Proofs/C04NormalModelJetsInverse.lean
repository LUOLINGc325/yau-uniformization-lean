import Yau.Proofs.C04BoundedGeometryChartsOperatorInverse
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Uniform jets of the same pointwise operator inverse, without shrinking
the source ball. Constants precede both the ball and the operator family. -/

noncomputable section
open Set Finset
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem normal_model_inverse_contDiffOn (A : E → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (R : ℝ) (hnear : ∀ x ∈ Metric.ball (0 : E) R,
      ‖A x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) :
    ContDiffOn ℝ ∞ (fun x => (A x).inverse) (Metric.ball (0 : E) R) := by
  intro x hx
  have hi := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one (A x)
    ((hnear x hx).trans_lt (by norm_num))
  exact (hi.contDiffAt_map_inverse.comp x hA.contDiffAt).contDiffWithinAt

theorem exists_normal_inverse_jet_bounds (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) :
    ∃ P : ℕ → ℝ, (∀ m, 0 < P m) ∧
      ∀ R : ℝ, 0 < R → ∀ A : E → E →L[ℝ] E,
        ContDiff ℝ ∞ A →
        (∀ x ∈ Metric.ball (0 : E) R,
          ‖A x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) →
        (∀ m x, x ∈ Metric.ball (0 : E) R → ‖iteratedFDeriv ℝ m A x‖ ≤ B m) →
        ContDiffOn ℝ ∞ (fun x => (A x).inverse) (Metric.ball (0 : E) R) ∧
          ∀ m x, x ∈ Metric.ball (0 : E) R →
            ‖iteratedFDeriv ℝ m (fun y => (A y).inverse) x‖ ≤ P m := by
  obtain ⟨C, hCpos, hCb⟩ := C04ChartsAux.exists_operator_inverse_jet_bounds (E := E)
  let D : ℕ → ℝ := fun m => 1 + ∑ j ∈ Finset.range (m + 1), B j
  let H : ℕ → ℝ := fun m => 1 + ∑ j ∈ Finset.range (m + 1), C j
  have hD (m : ℕ) : 1 ≤ D m := by
    dsimp [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j hj => (hB j).le)
  have hH (m : ℕ) : 1 ≤ H m := by
    dsimp [H]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun j hj => (hCpos j).le)
  have hBD (m j : ℕ) (hj : j ≤ m) : B j ≤ D m := by
    have hh : B j ≤ ∑ i ∈ Finset.range (m + 1), B i :=
      Finset.single_le_sum (fun i hi => (hB i).le) (Finset.mem_range.mpr (by omega))
    dsimp [D]
    linarith
  have hCH (m j : ℕ) (hj : j ≤ m) : C j ≤ H m := by
    have hh : C j ≤ ∑ i ∈ Finset.range (m + 1), C i :=
      Finset.single_le_sum (fun i hi => (hCpos i).le) (Finset.mem_range.mpr (by omega))
    dsimp [H]
    linarith
  let P : ℕ → ℝ := fun m => (m.factorial : ℝ) * H m * (D m) ^ m
  have hP (m : ℕ) : 0 < P m := by
    have hd : 0 < D m := zero_lt_one.trans_le (hD m)
    have hh : 0 < H m := zero_lt_one.trans_le (hH m)
    dsimp [P]
    positivity
  refine ⟨P, hP, ?_⟩
  intro R hR A hA hnear hjet
  refine ⟨normal_model_inverse_contDiffOn A hA R hnear, ?_⟩
  let T := Metric.ball (ContinuousLinearMap.id ℝ E) (1 / 2 : ℝ)
  have hmaps : MapsTo A (Metric.ball (0 : E) R) T := by
    intro x hx
    simpa only [T, Metric.mem_ball, dist_eq_norm] using
      (hnear x hx).trans_lt (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  have hInv : ContDiffOn ℝ ∞
      (ContinuousLinearMap.inverse : (E →L[ℝ] E) → E →L[ℝ] E) T := by
    intro L hL
    have hn : ‖L - ContinuousLinearMap.id ℝ E‖ < (1 / 2 : ℝ) := by
      simpa only [T, Metric.mem_ball, dist_eq_norm] using hL
    exact (Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one L
      (hn.trans (by norm_num))).contDiffAt_map_inverse.contDiffWithinAt
  intro m x hx
  have hbInv (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j
        (ContinuousLinearMap.inverse : (E →L[ℝ] E) → E →L[ℝ] E) T (A x)‖ ≤ H m := by
    rw [iteratedFDerivWithin_of_isOpen j Metric.isOpen_ball (hmaps hx)]
    exact (hCb j (A x) ((hnear x hx).trans (by norm_num))).trans (hCH m j hj)
  have hbA (j : ℕ) (hjpos : 1 ≤ j) (hj : j ≤ m) :
      ‖iteratedFDerivWithin ℝ j A (Metric.ball (0 : E) R) x‖ ≤ (D m) ^ j := by
    rw [iteratedFDerivWithin_of_isOpen j Metric.isOpen_ball hx]
    exact (hjet j x hx).trans ((hBD m j hj).trans (le_self_pow₀ (hD m) (by omega)))
  have hh := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) hInv hA.contDiffOn
    (by simp : (m : ℕ∞ω) ≤ ∞) Metric.isOpen_ball.uniqueDiffOn
    Metric.isOpen_ball.uniqueDiffOn hmaps hx hbInv hbA
  rw [iteratedFDerivWithin_of_isOpen m Metric.isOpen_ball hx] at hh
  exact hh

end Yau.Proofs.C04Aux
