import Yau.Proofs.Y01GridModels

/-! The original shrinking-chart jet estimate gives uniform fixed-order
transition bounds before the homological construction is started. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment

theorem jetNorm_mono {n d e : ℕ} (f : ComplexVector n → ComplexVector n) (hde : d ≤ e) :
    jetNorm f d ≤ jetNorm f e := by
  unfold jetNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun m hm hnot => norm_nonneg _)

theorem uniform_transition_jet_bound
    {n : ℕ} {X : KahlerManifold n} {o : Pt X} {h : Flow X} {ρ : STF X}
    {r₀ r₁ σ C Cb t₀ : ℝ} {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {f : ℝ → Pt X → ComplexVector n}
    (hcharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f) (d : ℕ) :
    ∃ B Td : ℝ, 0 ≤ B ∧ ∀ t t', Td ≤ t → t ≤ t' → jetNorm (F t t') d ≤ B := by
  obtain ⟨hr₁, hr₁r₀, hσ, hC, hunit, htransition, hcocycle, hcenter,
    hinverseCharts, hdecay, hjets, hsmall⟩ := hcharts
  obtain ⟨B, Td, hbound⟩ := hjets d
  refine ⟨|B|, Td, abs_nonneg B, ?_⟩
  intro t t' ht htt'
  have hm0 : 0 ≤ min 1 (Real.exp (B * ρ o t - σ * ρ o t')) :=
    le_min zero_le_one (Real.exp_pos _).le
  have hm1 : min 1 (Real.exp (B * ρ o t - σ * ρ o t')) ≤ 1 := min_le_left _ _
  calc
    _ ≤ B * min 1 (Real.exp (B * ρ o t - σ * ρ o t')) := hbound t t' ht htt'
    _ ≤ |B| * min 1 (Real.exp (B * ρ o t - σ * ρ o t')) :=
      mul_le_mul_of_nonneg_right (le_abs_self B) hm0
    _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left hm1 (abs_nonneg B)
    _ = _ := mul_one _

theorem constant_le_real_power {B s : ℝ} (hB : 0 ≤ B) (hs : 1 ≤ s) :
    B ≤ (1 + s) ^ (B / Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ B / Real.log 2 := div_nonneg hB hlog.le
  have hexp : (2 : ℝ) ^ (B / Real.log 2) = Real.exp B := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    field_simp
  calc
    B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
    _ = (2 : ℝ) ^ (B / Real.log 2) := hexp.symm
    _ ≤ (1 + s) ^ (B / Real.log 2) := Real.rpow_le_rpow (by norm_num) (by linarith) hC

theorem gridClock_one_le {Q : ℕ → ℝ} {N j₀ : ℕ} {M hm : ℝ}
    (hhm : 0 ≤ hm) (hgrid : GridLayout Q N M hm j₀) (k : ℕ) :
    1 ≤ gridClock Q N M hm j₀ k := by
  have h0 : 1 ≤ gridClock Q N M hm j₀ 0 := by
    rw [hgrid.1]
    exact Real.one_le_exp (mul_nonneg hhm (Nat.cast_nonneg j₀))
  exact h0.trans (hgrid.2.1.monotone (Nat.zero_le k))

theorem regular_transition_polynomial_bound
    {n d : ℕ} {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {tk s : ℕ → ℝ} {reg : ℕ → Prop} {B Td : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ t t', Td ≤ t → t ≤ t' → jetNorm (F t t') d ≤ B)
    (htk : StrictMono tk) (hTd : Td ≤ tk 0) (hs : ∀ k, 1 ≤ s k) :
    ∀ m ≤ d, ∃ C : ℝ, ∀ k, reg k → jetNorm (F (tk k) (tk (k + 1))) m ≤ (1 + s k) ^ C := by
  intro m hm
  refine ⟨B / Real.log 2, ?_⟩
  intro k hk
  exact (jetNorm_mono _ hm).trans ((hbound _ _ (hTd.trans (htk.monotone (Nat.zero_le k)))
    (htk.monotone (Nat.le_succ k))).trans (constant_le_real_power hB (hs k)))

end Yau.Proofs.Y01Aux
