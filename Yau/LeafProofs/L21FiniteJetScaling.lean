import Mathlib

/-! Shrinking a smooth germ makes any prescribed finite jet small.  The
positive-order factors are powers of the dilation parameter. -/

open Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def dilationEquiv (r : ℝ) (hr : r ≠ 0) : E ≃L[ℝ] E where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℝ E r hr
  continuous_toFun := continuous_const_smul r
  continuous_invFun := continuous_const_smul r⁻¹

@[simp] theorem dilationEquiv_apply (r : ℝ) (hr : r ≠ 0) (z : E) :
    dilationEquiv r hr z = r • z := rfl

theorem dilationEquiv_coe (r : ℝ) (hr : r ≠ 0) :
    (dilationEquiv (E := E) r hr : E →L[ℝ] E) = r • ContinuousLinearMap.id ℝ E := by
  ext z
  rfl

theorem iteratedFDeriv_dilate (f : E → F) (k : ℕ) (r : ℝ) (hr : r ≠ 0) (z : E) :
    iteratedFDeriv ℝ k (fun y => f (r • y)) z =
      (iteratedFDeriv ℝ k f (r • z)).compContinuousLinearMap
        (fun _ => r • ContinuousLinearMap.id ℝ E) := by
  have he := (dilationEquiv (E := E) r hr).iteratedFDerivWithin_comp_right
    f uniqueDiffOn_univ (x := z) (by trivial) k
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ,
    Function.comp_def, dilationEquiv_apply, dilationEquiv_coe] using he

theorem norm_iteratedFDeriv_dilate_le (f : E → F) (k : ℕ) (r : ℝ) (hr : r ≠ 0) (z : E) :
    ‖iteratedFDeriv ℝ k (fun y => f (r • y)) z‖ ≤
      ‖iteratedFDeriv ℝ k f (r • z)‖ * |r| ^ k := by
  rw [iteratedFDeriv_dilate f k r hr]
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (r • z)‖ *
        ∏ _ : Fin k, ‖r • ContinuousLinearMap.id ℝ E‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ k f (r • z)‖ * ∏ _ : Fin k, |r| := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg r) ContinuousLinearMap.norm_id_le
    _ = _ := by simp

theorem eventually_finite_jet_bounded {f : E → F}
    (hf : ContDiffAt ℝ ∞ f 0) (q : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 (0 : E),
      ∀ k ≤ q, ‖iteratedFDeriv ℝ k f y‖ ≤ B := by
  let B := 1 + ∑ k : Fin (q + 1), ‖iteratedFDeriv ℝ (k : ℕ) f 0‖
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  have hk (k : Fin (q + 1)) : ∀ᶠ y in 𝓝 (0 : E),
      ‖iteratedFDeriv ℝ (k : ℕ) f y‖ < ‖iteratedFDeriv ℝ (k : ℕ) f 0‖ + 1 :=
    (hf.continuousAt_iteratedFDeriv (k := k) (by simp)).norm.eventually_lt_const (by linarith)
  have hall : ∀ᶠ y in 𝓝 (0 : E), ∀ k : Fin (q + 1),
      ‖iteratedFDeriv ℝ (k : ℕ) f y‖ < ‖iteratedFDeriv ℝ (k : ℕ) f 0‖ + 1 :=
    Filter.eventually_all.mpr hk
  filter_upwards [hall] with y hy k hkq
  let j : Fin (q + 1) := ⟨k, by omega⟩
  have hs : ‖iteratedFDeriv ℝ k f 0‖ ≤ ∑ j : Fin (q + 1), ‖iteratedFDeriv ℝ (j : ℕ) f 0‖ :=
    Finset.single_le_sum (f := fun j : Fin (q + 1) => ‖iteratedFDeriv ℝ (j : ℕ) f 0‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  exact (hy j).le.trans (by dsimp [B]; linarith)

/-- The order `q` and the tolerance are chosen before the dilation radius.
There is no simultaneous smallness requirement on all infinitely many jets. -/
theorem exists_dilate_finite_jet_small_le {f : E → F}
    (hf : ContDiffAt ℝ ∞ f 0) (h0 : f 0 = 0) (q : ℕ)
    {δ b : ℝ} (hδ : 0 < δ) (hb : 0 < b) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r ≤ b ∧
      ∀ k ≤ q, ∀ z ∈ Metric.closedBall (0 : E) 2,
        ‖iteratedFDeriv ℝ k (fun y => f (r • y)) z‖ ≤ δ := by
  obtain ⟨B, hB, hbound⟩ := eventually_finite_jet_bounded hf q
  have hsmall : ∀ᶠ y in 𝓝 (0 : E), ‖f y‖ < δ :=
    hf.continuousAt.norm.eventually_lt_const (by simpa [h0] using hδ)
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (hbound.and hsmall)
  let r := min (a / 4) (min (1 / 2 : ℝ) (min b (δ / (2 * B))))
  have hr : 0 < r := lt_min (by positivity)
    (lt_min (by norm_num) (lt_min hb (by positivity)))
  have hra : r ≤ a / 4 := min_le_left _ _
  have hrhalf : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hrb : r ≤ b := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrδ : r ≤ δ / (2 * B) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr1 : r ≤ 1 := by linarith
  have hBr : B * r ≤ δ := by
    have hh := (le_div_iff₀ (show 0 < 2 * B by positivity)).mp hrδ
    nlinarith
  refine ⟨r, hr, hr1, hrb, ?_⟩
  intro k hk z hz
  have hzn : ‖z‖ ≤ 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hza : r • z ∈ Metric.ball (0 : E) a := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hgood := hball hza
  by_cases hk0 : k = 0
  · subst k
    simpa only [norm_iteratedFDeriv_zero] using hgood.2.le
  · have hpow : r ^ k ≤ r := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      rw [pow_succ]
      exact mul_le_of_le_one_left hr.le (pow_le_one₀ hr.le hr1)
    calc
      _ ≤ ‖iteratedFDeriv ℝ k f (r • z)‖ * |r| ^ k :=
        norm_iteratedFDeriv_dilate_le f k r hr.ne' z
      _ ≤ B * r ^ k := by rw [abs_of_pos hr]; gcongr; exact hgood.1 k hk
      _ ≤ B * r := mul_le_mul_of_nonneg_left hpow hB.le
      _ ≤ δ := hBr

theorem exists_dilate_finite_jet_small {f : E → F}
    (hf : ContDiffAt ℝ ∞ f 0) (h0 : f 0 = 0) (q : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ k ≤ q, ∀ z ∈ Metric.closedBall (0 : E) 2,
        ‖iteratedFDeriv ℝ k (fun y => f (r • y)) z‖ ≤ δ := by
  obtain ⟨r, hr, hr1, _, hjet⟩ :=
    exists_dilate_finite_jet_small_le hf h0 q hδ (show (0 : ℝ) < 1 by norm_num)
  exact ⟨r, hr, hr1, hjet⟩

end Yau.LeafProofs.L21Aux
