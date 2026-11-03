import Yau.Proofs.C03EnvelopeSmoothingUniform
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! One radius is chosen after the compact strict set and the continuous positive field. -/
noncomputable section
open scoped Topology Matrix ComplexOrder
open Set Metric
namespace Yau.Proofs.C03Aux.EnvelopeSmoothing
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem exists_common_smoothing_radius (R rEnv : ℝ) (hR : 0 < R) (hRenv : R < rEnv)
    (S T : Set (ComplexVector n)) (hS : IsOpen S) (hT : IsCompact T)
    (hTS : T ⊆ S) (hTD : T ⊆ ball 0 R)
    (H : ComplexVector n → Herm n) (hHc : ∀ i j, Continuous (fun z => H z i j))
    (hHp : ∀ z, (H z).PosDef) :
    ∃ s d : ℝ, 0 < s ∧ R < s ∧ s < rEnv ∧ 0 < d ∧
      (∀ z ∈ ball (0 : ComplexVector n) R, ∀ a ∈ closedBall (0 : ComplexVector n) d,
        z - a ∈ ball (0 : ComplexVector n) s) ∧
      ∀ z ∈ T,
        ball z (3 * d) ⊆ S ∧ ball z (3 * d) ⊆ ball (0 : ComplexVector n) s ∧
          ∀ q ∈ ball z (3 * d), ∀ v,
            (1 / 2 : ℝ) * matrixQuadratic (H z) v ≤ matrixQuadratic (H q) v := by
  let s : ℝ := (R + rEnv) / 2
  have hRs : R < s := by dsimp only [s]; linarith
  have hsEnv : s < rEnv := by dsimp only [s]; linarith
  obtain ⟨rho, hrho, hrhoS⟩ := hT.exists_cthickening_subset_open hS hTS
  obtain ⟨dH, hdH, hcompare⟩ := exists_uniform_relative_matrix_radius H hHc hHp T hT
  let d : ℝ := min ((s - R) / 4) (min (rho / 4) (dH / 4))
  have hd : 0 < d := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hdgap : d ≤ (s - R) / 4 := min_le_left _ _
  have hdrho : d ≤ rho / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hdHbound : d ≤ dH / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have h3rho : 3 * d ≤ rho := by linarith
  have h3H : 3 * d ≤ dH := by linarith
  have h3gap : 3 * d + R ≤ s := by linarith
  refine ⟨s, d, hR.trans hRs, hRs, hsEnv, hd, ?_, ?_⟩
  · intro z hz a ha
    have ha' : ‖a‖ ≤ d := by simpa only [mem_closedBall, dist_zero_right] using ha
    have hz' : dist z 0 < R := mem_ball.mp hz
    apply mem_ball.mpr
    calc
      dist (z - a) 0 ≤ dist (z - a) z + dist z 0 := dist_triangle _ _ _
      _ = ‖a‖ + dist z 0 := by simp [dist_eq_norm]
      _ < d + R := add_lt_add_of_le_of_lt ha' hz'
      _ ≤ s := by linarith
  · intro z hz
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      apply hrhoS
      exact closedBall_subset_cthickening hz rho ((mem_ball.mp hq).le.trans h3rho)
    · intro q hq
      apply mem_ball.mpr
      calc
        dist q 0 ≤ dist q z + dist z 0 := dist_triangle _ _ _
        _ < 3 * d + R := add_lt_add (mem_ball.mp hq) (mem_ball.mp (hTD hz))
        _ ≤ s := h3gap
    · intro q hq v
      exact hcompare z hz q ((mem_ball.mp hq).trans_le h3H) v

end Yau.Proofs.C03Aux.EnvelopeSmoothing
