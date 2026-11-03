import Yau.Proofs.C01IntegratedHarnack
import Yau.Proofs.C01ScalarBasepointBound

/-! The proved integrated Harnack inequality and the genuine basepoint
bound give quadratic scalar growth in the actual positive-time distance.
The constant is uniform on a fixed finite time interval. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_quadratic_distance_bound
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ t, 0 < t → t ≤ T → ∀ x : Pt X,
      scalarCurvature (h t) x ≤
        C * (1 + inducedDistance (h t) x o ^ 2) / t := by
  obtain ⟨B₀, hB₀⟩ := localizedFlow_basepoint_scalar_bound hflow hjoint
  let B := max B₀ 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right B₀ 1)
  have hBbound (s : ℝ) (hs : 0 ≤ s) : scalarCurvature (h s) o ≤ B :=
    (hB₀ s hs).trans (le_max_left B₀ 1)
  let C := B * (T + 1) * Real.exp 1
  have hC : 0 < C := mul_pos (mul_pos hB (by linarith)) (Real.exp_pos 1)
  refine ⟨C, hC, ?_⟩
  intro t ht htT x
  let d := inducedDistance (h t) x o
  let s := t + 1 + d ^ 2
  have hd : 0 ≤ d ^ 2 := sq_nonneg d
  have hden : 0 < 1 + d ^ 2 := by linarith
  have hts : t < s := by dsimp only [s]; linarith
  have hs : 0 < s := ht.trans hts
  have htime : s ≤ (T + 1) * (1 + d ^ 2) := by
    dsimp only [s]
    nlinarith [mul_nonneg hT hd]
  have hratio : d ^ 2 / (s - t) ≤ 1 := by
    rw [div_le_one (sub_pos.mpr hts)]
    dsimp only [s]
    linarith
  have hexp : Real.exp (d ^ 2 / (s - t)) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hratio
  have hH := localizedFlow_scalar_integrated_distance_harnack hflow hjoint x o t s ht hts
  have hfirst : scalarCurvature (h s) o * (s / t) * Real.exp (d ^ 2 / (s - t)) ≤
      B * (s / t) * Real.exp 1 :=
    mul_le_mul
      (mul_le_mul_of_nonneg_right (hBbound s hs.le) (div_pos hs ht).le)
      hexp (Real.exp_pos _).le (mul_nonneg hB.le (div_pos hs ht).le)
  have hsecond : B * (s / t) * Real.exp 1 ≤ C * (1 + d ^ 2) / t := by
    calc
      _ ≤ B * (((T + 1) * (1 + d ^ 2)) / t) * Real.exp 1 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htime ht.le) hB.le)
          (Real.exp_pos 1).le
      _ = _ := by dsimp only [C]; ring
  exact hH.trans (hfirst.trans hsecond)

end Yau.NodeProofs.C01Aux
