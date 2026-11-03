import Yau.LeafProofs.L21FiniteJetScaling

/-! One finite dilation, chosen from uniform jet bounds before the function. -/

noncomputable section
open Set Finset
open scoped ContDiff Topology

namespace Yau.Proofs.C04Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem uniform_finite_dilation_le {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (q : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 < B j) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ d ≤ R / 4 ∧ ∀ f : E → F,
      ContDiffOn ℝ ∞ f (Metric.ball 0 R) → f 0 = 0 →
      (∀ j, j ≤ q + 1 → ∀ x ∈ Metric.ball 0 R, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) →
      ∀ j, j ≤ q → ∀ x ∈ Metric.ball 0 (2 : ℝ),
        ‖iteratedFDeriv ℝ j (fun y => f (d • y)) x‖ ≤ ε := by
  let M := 1 + ∑ j : Fin (q + 2), B j
  have hsum : 0 ≤ ∑ j : Fin (q + 2), B j :=
    Finset.sum_nonneg fun j hj => (hB j).le
  have hM : 0 < M := by dsimp only [M]; linarith
  have hMj : ∀ j, j ≤ q + 1 → B j ≤ M := by
    intro j hj
    let k : Fin (q + 2) := ⟨j, by omega⟩
    have hh : B j ≤ ∑ k : Fin (q + 2), B k :=
      Finset.single_le_sum (f := fun k : Fin (q + 2) => B k)
        (fun k hk => (hB k).le) (Finset.mem_univ k)
    dsimp only [M]
    linarith
  let d := min (R / 4) (min 1 (ε / (4 * M)))
  have hd : 0 < d := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  have hdR : d ≤ R / 4 := min_le_left _ _
  have hd1 : d ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdε : d ≤ ε / (4 * M) := (min_le_right _ _).trans (min_le_right _ _)
  have hMd : 4 * M * d ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < 4 * M by positivity)).mp hdε
    nlinarith
  refine ⟨d, hd, hd1, hdR, ?_⟩
  intro f hf hf0 hjet j hj x hx
  have hxn : ‖x‖ < 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hdx : d • x ∈ Metric.ball (0 : E) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hd]
    nlinarith
  by_cases hj0 : j = 0
  · subst j
    rw [norm_iteratedFDeriv_zero]
    have hdiff : ∀ y ∈ Metric.ball (0 : E) R, DifferentiableAt ℝ f y := by
      intro y hy
      exact ((hf y hy).contDiffAt (Metric.isOpen_ball.mem_nhds hy)).differentiableAt (by simp)
    have hderiv : ∀ y ∈ Metric.ball (0 : E) R, ‖fderiv ℝ f y‖ ≤ M := by
      intro y hy
      rw [← norm_iteratedFDeriv_one]
      exact (hjet 1 (by omega) y hy).trans (hMj 1 (by omega))
    have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hderiv
      (convex_ball (0 : E) R) (Metric.mem_ball_self hR) hdx
    rw [hf0, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hd] at hmean
    have hsmall : M * (d * ‖x‖) ≤ 2 * M * d := by
      calc
        M * (d * ‖x‖) = (M * d) * ‖x‖ := by ring
        _ ≤ (M * d) * 2 := mul_le_mul_of_nonneg_left hxn.le (mul_pos hM hd).le
        _ = 2 * M * d := by ring
    exact hmean.trans (hsmall.trans (by nlinarith))
  · have hpow : d ^ j ≤ d := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      rw [pow_succ]
      exact mul_le_of_le_one_left hd.le (pow_le_one₀ hd.le hd1)
    calc
      ‖iteratedFDeriv ℝ j (fun y => f (d • y)) x‖ ≤
          ‖iteratedFDeriv ℝ j f (d • x)‖ * |d| ^ j :=
        Yau.LeafProofs.L21Aux.norm_iteratedFDeriv_dilate_le f j d hd.ne' x
      _ ≤ M * d ^ j := by
        rw [abs_of_pos hd]
        gcongr
        exact (hjet j (by omega) (d • x) hdx).trans (hMj j (by omega))
      _ ≤ M * d := mul_le_mul_of_nonneg_left hpow hM.le
      _ ≤ ε := by nlinarith

theorem uniform_finite_dilation {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (q : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 < B j) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ f : E → F,
      ContDiffOn ℝ ∞ f (Metric.ball 0 R) → f 0 = 0 →
      (∀ j, j ≤ q + 1 → ∀ x ∈ Metric.ball 0 R, ‖iteratedFDeriv ℝ j f x‖ ≤ B j) →
      ∀ j, j ≤ q → ∀ x ∈ Metric.ball 0 (2 : ℝ),
        ‖iteratedFDeriv ℝ j (fun y => f (d • y)) x‖ ≤ ε := by
  obtain ⟨d, hd, hd1, hdR, hsmall⟩ := uniform_finite_dilation_le (E := E) (F := F) hR hε q B hB
  exact ⟨d, hd, hd1, hsmall⟩

end Yau.Proofs.C04Aux
