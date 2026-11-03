import Yau.Proofs.P04SmoothSeries

noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

namespace Yau.Proofs.P04Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Summable global derivative bounds identify the derivatives of the SAME
series as the limit of its actual finite partial sums. -/
theorem partial_sum_derivative_tendsto (f : ℕ → E → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (v : ℕ → ℕ → ℝ)
    (hv : ∀ q, Summable (v q))
    (hbound : ∀ q i x, ‖iteratedFDeriv ℝ q (f i) x‖ ≤ v q i)
    (q : ℕ) (x : E) :
    Tendsto (fun N => iteratedFDeriv ℝ q (fun y => ∑ i ∈ Finset.range N, f i y) x)
      atTop (𝓝 (iteratedFDeriv ℝ q (fun y => ∑' i, f i y) x)) := by
  rw [iteratedFDeriv_tsum_apply hf (fun k _ => hv k) (fun k i y _ => hbound k i y) (by simp) x]
  have hs : Summable (fun i => iteratedFDeriv ℝ q (f i) x) :=
    Summable.of_norm_bounded (hv q) (fun i => hbound q i x)
  convert hs.hasSum.tendsto_sum_nat using 1
  funext N
  exact iteratedFDeriv_fun_sum_apply (fun i _ => ((hf i).of_le (by simp)).contDiffAt)

/-- Compact chart extensions provide all bounds first; one coefficient
sequence then gives smooth sums and convergence of every actual derivative. -/
theorem exists_coefficients_with_smooth_sums_and_jets (b : ℕ → ℕ → E → ℝ)
    (hb : ∀ i j, ContDiff ℝ ∞ (b i j)) (hcompact : ∀ i j, HasCompactSupport (b i j))
    (B : ℕ → ℝ) :
    ∃ c : ℕ → ℝ,
      (∀ i, 0 < c i ∧ c i*Real.exp (B i) ≤ (1/2 : ℝ)^i) ∧
      ∀ j, ContDiff ℝ ∞ (fun x => ∑' i, c i*b i j x) ∧
        ∀ q x, Tendsto (fun N => iteratedFDeriv ℝ q
          (fun y => ∑ i ∈ Finset.range N, c i*b i j y) x)
          atTop (𝓝 (iteratedFDeriv ℝ q (fun y => ∑' i, c i*b i j y) x)) := by
  classical
  obtain ⟨D,hD⟩ := exists_global_derivative_budgets b hb hcompact
  obtain ⟨c,hc⟩ := exists_positive_diagonal_coefficients B D
  let v : ℕ → ℕ → ℕ → ℝ := fun j q i => if i < max j q then c i*D i j q else (1/2 : ℝ)^i
  have hv (j q : ℕ) : Summable (v j q) := by
    apply geometric_half_hasSum.summable.congr_cofinite
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop (max j q)] with i hi
    simp only [v,if_neg (not_lt.mpr hi)]
  have hbound (j q i : ℕ) (x : E) :
      ‖iteratedFDeriv ℝ q (fun y => c i*b i j y) x‖ ≤ v j q i := by
    have hderiv : iteratedFDeriv ℝ q (fun y => c i*b i j y) x =
        c i • iteratedFDeriv ℝ q (b i j) x := by
      simpa only [smul_eq_mul] using
        (iteratedFDeriv_const_smul_apply' (a := c i) (i := q) (x := x)
          ((hb i j).of_le (by simp)).contDiffAt)
    rw [hderiv,norm_smul,Real.norm_eq_abs,abs_of_pos (hc i).1]
    have HH := mul_le_mul_of_nonneg_left ((hD i j q).2 x) (hc i).1.le
    dsimp only [v]
    split_ifs with hi
    · exact HH
    · have hij : j ≤ i := (le_max_left j q).trans (le_of_not_gt hi)
      have hiq : q ≤ i := (le_max_right j q).trans (le_of_not_gt hi)
      have Hc := (hc i).2.2 j hij q hiq
      rw [abs_of_nonneg (hD i j q).1] at Hc
      exact HH.trans Hc
  have hf (i j : ℕ) : ContDiff ℝ ∞ (fun x => c i*b i j x) := contDiff_const.mul (hb i j)
  refine ⟨c,fun i => ⟨(hc i).1,(hc i).2.1⟩,fun j => ⟨?_,?_⟩⟩
  · exact contDiff_tsum (fun i => hf i j) (fun q _ => hv j q) (fun q i x _ => hbound j q i x)
  · exact fun q x => partial_sum_derivative_tendsto _ (fun i => hf i j) (v j) (hv j) (hbound j) q x

end Yau.Proofs.P04Aux
