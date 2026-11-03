import Yau.Proofs.C02DoubleHomotopyBound
import Yau.Proofs.C02FirstExit

/-! A first-exit bootstrap on one fixed radius. The actual homotopy
identities and curvature bound imply the zeroth-order gauge estimate;
no initially assumed differential bound survives in the conclusion. -/

noncomputable section
open Set
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance low_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance low_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance low_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance low_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance low_two_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance low_two_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem radial_low_order_bootstrap
    (A : E → E →L[ℝ] E →L[ℝ] E) (B : E → E →L[ℝ] E)
    (F : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (hBcont : Continuous B) (hB0 : B 0 = ContinuousLinearMap.id ℝ E)
    (hA : ∀ y, A y = radialHomotopy F y)
    (hB : ∀ y, B y = ContinuousLinearMap.id ℝ E + radialHomotopy (fun z => (A z).flip) y)
    {ρ K : ℝ} (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (hsmall : K * ρ ^ 2 ≤ 1 / 16)
    (hF : ∀ y, ‖y‖ ≤ ρ → ‖F y‖ ≤ K * ‖B y‖ ^ 2) :
    ∀ x, ‖x‖ ≤ ρ → ‖B x - ContinuousLinearMap.id ℝ E‖ ≤ 9 / 256 ∧ ‖B x‖ ≤ 3 / 2 := by
  have hscale (y : E) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ‖s • y‖ ≤ ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg y) hs.2
  have hImprove (y : E) (hy : ‖y‖ ≤ ρ)
      (hprev : ∀ s ∈ Icc (0 : ℝ) 1, ‖B (s • y)‖ ≤ 3 / 2) :
      ‖B y - ContinuousLinearMap.id ℝ E‖ ≤ 9 / 256 ∧ ‖B y‖ < 3 / 2 := by
    have hFC : ∀ s ∈ Icc (0 : ℝ) 1, ‖F (s • y)‖ ≤ K * (3 / 2) ^ 2 := by
      intro s hs
      exact (hF _ ((hscale y s hs).trans hy)).trans
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hprev s hs)) hK)
    have hb := double_radial_homotopy_bound A B F hA hB y (by positivity) hFC
    have hKy : K * ‖y‖ ^ 2 ≤ 1 / 16 :=
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg y) hρ).mpr hy) hK).trans hsmall
    have hc : ‖B y - ContinuousLinearMap.id ℝ E‖ ≤ 9 / 256 := by nlinarith
    have hN : ‖B y‖ ≤ ‖B y - ContinuousLinearMap.id ℝ E‖ + 1 := by
      calc
        _ = ‖(B y - ContinuousLinearMap.id ℝ E) + ContinuousLinearMap.id ℝ E‖ := by rw [sub_add_cancel]
        _ ≤ ‖B y - ContinuousLinearMap.id ℝ E‖ + ‖ContinuousLinearMap.id ℝ E‖ := norm_add_le _ _
        _ ≤ _ := add_le_add_right (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)) _
    exact ⟨hc, by linarith⟩
  intro x hx
  have hf : Continuous (fun t : ℝ => ‖B (t • x)‖) :=
    (hBcont.comp (continuous_id.smul continuous_const)).norm
  have hzero : ‖B ((0 : ℝ) • x)‖ < (3 / 2 : ℝ) := by
    rw [zero_smul, hB0]
    have hn := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
    linarith
  have hBefore : ∀ t ∈ Icc (0 : ℝ) 1, ‖B (t • x)‖ < 3 / 2 := by
    apply first_exit_barrier hf hzero
    intro t ht hprev
    apply (hImprove (t • x) ((hscale x t ht).trans hx) ?_).2
    intro s hs
    rw [smul_smul]
    exact hprev (s * t) ⟨mul_nonneg hs.1 ht.1, mul_le_of_le_one_left ht.1 hs.2⟩
  have hb := hImprove x hx (fun s hs => (hBefore s hs).le)
  exact ⟨hb.1, hb.2.le⟩

end Yau.Blueprint.C02Proof
