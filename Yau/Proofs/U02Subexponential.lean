import Yau.Blueprint.Nodes

/-! Absorption of the original coefficient errors into exponential margins. -/

open scoped Topology
open Filter

namespace Yau.NodeProofs.U02Proof

theorem subexponential_absorption {s eta : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) (heta : Tendsto eta atTop (𝓝 0))
    (C : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, C * Real.exp (eta k * s k) ≤ Real.exp (eps * s k) := by
  have hh : 0 < eps / 2 := by positivity
  have hC : ∀ᶠ k in atTop, C ≤ Real.exp ((eps / 2) * s k) :=
    (tendsto_atTop.1 (Real.tendsto_exp_atTop.comp (hs.const_mul_atTop hh))) C
  have he : ∀ᶠ k in atTop, eta k < eps / 2 :=
    heta.eventually (gt_mem_nhds hh)
  filter_upwards [hC, he, (tendsto_atTop.1 hs) 0] with k hk hek hsk
  calc
    C * Real.exp (eta k * s k) ≤
        Real.exp ((eps / 2) * s k) * Real.exp (eta k * s k) :=
      mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
    _ = Real.exp ((eps / 2) * s k + eta k * s k) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (eps * s k) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hek.le hsk
      linarith

theorem subexponential_times_decay {s eta : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) (heta : Tendsto eta atTop (𝓝 0))
    (C a b : ℝ) (hab : b < a) :
    ∀ᶠ k in atTop,
      C * Real.exp (eta k * s k) * Real.exp (-a * s k) ≤ Real.exp (-b * s k) := by
  filter_upwards [subexponential_absorption hs heta C (sub_pos.mpr hab)] with k hk
  calc
    C * Real.exp (eta k * s k) * Real.exp (-a * s k) ≤
        Real.exp ((a - b) * s k) * Real.exp (-a * s k) :=
      mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
    _ = Real.exp (-b * s k) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Yau.NodeProofs.U02Proof
