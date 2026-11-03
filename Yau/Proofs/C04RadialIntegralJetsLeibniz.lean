import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Leibniz with the identity: only two terms survive, so the highest jet
retains a radius coefficient independent of its order. -/

noncomputable section
open Finset
open scoped ContDiff

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem radialIntegral_norm_id_jet_ge_two {m : ℕ} (hm : 2 ≤ m) (x : E) :
    ‖iteratedFDeriv ℝ m (id : E → E) x‖ = 0 := by
  have hfid : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E := by
    funext y
    exact fderiv_id
  have hm' : m = (m - 2 + 1) + 1 := by omega
  rw [hm', ← norm_iteratedFDeriv_fderiv, hfid]
  simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]

theorem radialIntegral_eval_leibniz (g : E → E →L[ℝ] G) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => g y y) x‖ ≤
      ‖iteratedFDeriv ℝ m g x‖ * ‖x‖ + (m : ℝ) * ‖iteratedFDeriv ℝ (m - 1) g x‖ := by
  have hb := (ContinuousLinearMap.id ℝ (E →L[ℝ] G)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    hg (contDiff_id : ContDiff ℝ ∞ (id : E → E)) x (by simp : (m : ℕ∞ω) ≤ ∞)
    ContinuousLinearMap.norm_id_le
  change ‖iteratedFDeriv ℝ m (fun y => g y y) x‖ ≤ _ at hb
  cases m with
  | zero =>
    simpa only [norm_iteratedFDeriv_zero, Nat.cast_zero, zero_mul, add_zero] using (g x).le_opNorm x
  | succ k =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hb
    have hz : ∑ i ∈ Finset.range k,
        ((k + 1).choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ *
          ‖iteratedFDeriv ℝ (k + 1 - i) (id : E → E) x‖ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [radialIntegral_norm_id_jet_ge_two (by have := Finset.mem_range.mp hi; omega)]
      ring
    rw [hz, zero_add] at hb
    have hsub : k + 1 - k = 1 := by omega
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.choose_succ_self_right,
      Nat.sub_self, hsub, norm_iteratedFDeriv_zero] at hb
    have hnorm : ‖iteratedFDeriv ℝ 1 (id : E → E) x‖ ≤ 1 := by
      rw [norm_iteratedFDeriv_one, fderiv_id]
      exact ContinuousLinearMap.norm_id_le
    have hnormOne : ‖iteratedFDeriv ℝ (k + 1 - k) (id : E → E) x‖ ≤ 1 := by
      rw [hsub]
      exact hnorm
    have hnormZero : ‖iteratedFDeriv ℝ (k + 1 - (k + 1)) (id : E → E) x‖ = ‖x‖ := by
      rw [Nat.sub_self, norm_iteratedFDeriv_zero]
      rfl
    rw [hnormZero] at hb
    have hmul := mul_le_mul_of_nonneg_left hnormOne
      (mul_nonneg (Nat.cast_nonneg (k + 1)) (norm_nonneg (iteratedFDeriv ℝ k g x)))
    change ‖iteratedFDeriv ℝ (k + 1) (fun y => g y y) x‖ ≤
      ‖iteratedFDeriv ℝ (k + 1) g x‖ * ‖x‖ + ((k + 1 : ℕ) : ℝ) * ‖iteratedFDeriv ℝ k g x‖
    nlinarith

theorem radialIntegral_dilate_jet_bound (f : E → E →L[ℝ] G) (hf : ContDiff ℝ ∞ f)
    {R t : ℝ} (hR : 0 ≤ R) (ht : t ∈ Set.Icc (0 : ℝ) 1) (B : ℕ → ℝ)
    (hB : ∀ j, 0 ≤ B j) (m : ℕ)
    (hbound : ∀ j, j ≤ m → ∀ x ∈ Metric.closedBall (0 : E) R, ‖iteratedFDeriv ℝ j f x‖ ≤ B j)
    {x : E} (hx : x ∈ Metric.closedBall (0 : E) R) :
    ‖iteratedFDeriv ℝ m (fun y => t • (f (t • y) y)) x‖ ≤
      R * B m + (m : ℝ) * B (m - 1) := by
  have hxn : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have htx : t • x ∈ Metric.closedBall (0 : E) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans hxn
  let g := fun y : E => f (t • y)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.smul contDiff_id)
  have hj : ∀ j, j ≤ m → ‖iteratedFDeriv ℝ j g x‖ ≤ B j := by
    intro j hj
    have heq := congrFun (iteratedFDeriv_comp_const_smul t (hf.of_le (by simp : (j : ℕ∞ω) ≤ ∞))) x
    rw [heq, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.1 ht.2)).trans
      (hbound j hj (t • x) htx)
  have heval : ContDiff ℝ ∞ (fun y : E => g y y) := hg.clm_apply contDiff_id
  have hscale := iteratedFDeriv_const_smul_apply' (a := t) (x := x)
    ((heval.contDiffAt).of_le (by simp : (m : ℕ∞ω) ≤ ∞))
  change ‖iteratedFDeriv ℝ m (fun y => t • (g y y)) x‖ ≤ _
  rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (fun y => g y y) x‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
    _ ≤ ‖iteratedFDeriv ℝ m g x‖ * ‖x‖ + (m : ℝ) * ‖iteratedFDeriv ℝ (m - 1) g x‖ :=
      radialIntegral_eval_leibniz g hg m x
    _ ≤ B m * R + (m : ℝ) * B (m - 1) := by
      gcongr
      · exact hB m
      · exact hj m (le_refl m)
      · exact hj (m - 1) (Nat.sub_le _ _)
    _ = R * B m + (m : ℝ) * B (m - 1) := by ring

end Yau.Proofs.C04Aux
