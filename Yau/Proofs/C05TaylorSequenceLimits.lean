import Yau.Proofs.C05TaylorSequenceBounds

/-! A fixed Taylor radius is chosen before passing to the family limit. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Yau.Proofs.C05TaylorSequenceAux
variable {ι : Type*} {l : Filter ι}

theorem deriv_tendsto_zero (f : ι → ℝ → ℝ) {δ M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hf : ∀ i, ContDiffOn ℝ 2 (f i) (Ioo (-δ) δ))
    (hnonneg : ∀ i t, t ∈ Ioo (-δ) δ → 0 ≤ f i t)
    (hbound : ∀ i t, t ∈ Ioo (-δ) δ → |iteratedDeriv 2 (f i) t| ≤ M)
    (hzero : Tendsto (fun i => f i 0) l (𝓝 0)) :
    Tendsto (fun i => deriv (f i) 0) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let r := min (δ/2) (ε/(M+1))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hMr : M*r ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < M+1 by positivity)).mp
      (min_le_right (δ/2) (ε/(M+1)))
    dsimp only [r] at *
    nlinarith
  have hsmall : ∀ᶠ i in l, f i 0 < ε*r/2 :=
    hzero.eventually (gt_mem_nhds (show (0:ℝ)<ε*r/2 by positivity))
  filter_upwards [hsmall] with i hi
  have hb := abs_deriv_zero_le (f i) hδ (hf i) (hnonneg i) (hbound i) hr hrδ
  have hd : f i 0/r < ε/2 := (div_lt_iff₀ hr).mpr (by nlinarith)
  rw [Real.dist_eq,sub_zero]
  linarith

theorem eventually_second_deriv_lower (f : ι → ℝ → ℝ) {δ M : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hf : ∀ i, ContDiffOn ℝ 3 (f i) (Ioo (-δ) δ))
    (hnonneg : ∀ i t, t ∈ Ioo (-δ) δ → 0 ≤ f i t)
    (hbound : ∀ i t, t ∈ Ioo (-δ) δ → |iteratedDeriv 3 (f i) t| ≤ M)
    (hzero : Tendsto (fun i => f i 0) l (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ i in l, -ε ≤ iteratedDeriv 2 (f i) 0 := by
  intro ε hε
  let r := min (δ/2) (ε/(M+1))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hMr : M*r ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < M+1 by positivity)).mp
      (min_le_right (δ/2) (ε/(M+1)))
    dsimp only [r] at *
    nlinarith
  have hsmall : ∀ᶠ i in l, f i 0 < ε*r^2/4 :=
    hzero.eventually (gt_mem_nhds (show (0:ℝ)<ε*r^2/4 by positivity))
  filter_upwards [hsmall] with i hi
  have hb := second_deriv_zero_lower (f i) hδ (hf i) (hnonneg i) (hbound i) hr hrδ
  have hd : 2*f i 0/r^2 ≤ ε/2 := (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith)
  have hn : -2*f i 0/r^2 = -(2*f i 0/r^2) := by ring
  rw [hn] at hb
  linarith

end Yau.Proofs.C05TaylorSequenceAux
