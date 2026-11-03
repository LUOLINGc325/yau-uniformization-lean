import Yau.LeafProofs.L03DivergenceEnergy

open MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure]

theorem integral_sq_tendsto_of_toLp_tendsto (f : ℕ → E → ℝ)
    (hf : ∀ m, MemLp (f m) 2 ν) (d : Lp ℝ 2 ν)
    (ht : Tendsto (fun m => (hf m).toLp (f m)) atTop (𝓝 d)) :
    Tendsto (fun m => ∫ x, ‖f m x - d x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  have heq (m : ℕ) : ‖(hf m).toLp (f m) - d‖ ^ 2 = ∫ x, ‖f m x - d x‖ ^ 2 ∂ν := by
    have hclass : ((hf m).sub (Lp.memLp d)).toLp ((f m) - (d : E → ℝ)) = (hf m).toLp (f m) - d := by
      rw [MemLp.toLp_sub (hf m) (Lp.memLp d), Lp.toLp_coeFn d (Lp.memLp d)]
    calc
      _ = ‖((hf m).sub (Lp.memLp d)).toLp ((f m) - (d : E → ℝ))‖ ^ 2 := by rw [hclass]
      _ = ∫ x, ((f m) - (d : E → ℝ)) x ^ 2 ∂ν := DivergenceEnergy.toLp_norm_sq ν _ _
      _ = _ := by simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  simpa only [heq, zero_pow (by decide : 2 ≠ 0)] using
    (tendsto_iff_norm_sub_tendsto_zero.mp ht).pow 2

/-- Completeness supplies actual compactly supported raw L² derivative
limits. Truncating the representatives to the common compact support
preserves strong convergence, without assuming any pointwise derivative
of the original rough value limit. -/
theorem exists_compact_gradient_limits {α ι : Type*} [Fintype α] [Fintype ι]
    (v : ι → E) (U : ℕ → E → α → ℝ)
    (hU : ∀ m c, ContDiff ℝ ∞ (fun x => U m x c))
    (K : Set E) (hK : IsCompact K)
    (hUK : ∀ m c, tsupport (fun x => U m x c) ⊆ K)
    (ht : Tendsto (fun p : ℕ × ℕ => ∫ x, DivergenceEnergy.gradientSq v
      (fun y c => U p.1 y c - U p.2 y c) x ∂ν) atTop (𝓝 0)) :
    ∃ D : E → ι × α → ℝ,
      (∀ q, MemLp (fun x => D x q) 2 ν) ∧
      (∀ q, tsupport (fun x => D x q) ⊆ K) ∧
      ∀ q, Tendsto (fun m => ∫ x, ‖DivergenceEnergy.derivative v (U m) x q - D x q‖ ^ 2 ∂ν)
        atTop (𝓝 0) := by
  classical
  have hcU (m : ℕ) (c : α) : HasCompactSupport (fun x => U m x c) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hUK m c)
  have hDm (m : ℕ) (q : ι × α) : MemLp (fun x => DivergenceEnergy.derivative v (U m) x q) 2 ν :=
    DivergenceEnergy.derivative_memLp ν v (U m) (hU m) (hcU m) q
  have hcauchy := DivergenceEnergy.gradient_cauchySeq_toLp ν v U hU hcU ht
  have hex (q : ι × α) : ∃ d : Lp ℝ 2 ν, Tendsto
      (fun m => (hDm m q).toLp (fun x => DivergenceEnergy.derivative v (U m) x q)) atTop (𝓝 d) :=
    cauchySeq_tendsto_of_complete (hcauchy q)
  choose d hd using hex
  let D : E → ι × α → ℝ := fun x q => K.indicator (fun y => d q y) x
  have hD (q : ι × α) : MemLp (fun x => D x q) 2 ν :=
    (Lp.memLp (d q)).indicator hK.isClosed.measurableSet.nullMeasurableSet
  refine ⟨D, hD, ?_, ?_⟩
  · intro q
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (by simp only [D, Set.indicator_of_notMem hn])
  · intro q
    have hlim := integral_sq_tendsto_of_toLp_tendsto ν
      (fun m x => DivergenceEnergy.derivative v (U m) x q) (fun m => hDm m q) (d q) (hd q)
    have hbound (m : ℕ) : (∫ x, ‖DivergenceEnergy.derivative v (U m) x q - D x q‖ ^ 2 ∂ν) ≤
        ∫ x, ‖DivergenceEnergy.derivative v (U m) x q - d q x‖ ^ 2 ∂ν := by
      apply integral_mono
        ((memLp_two_iff_integrable_sq_norm ((hDm m q).sub (hD q)).aestronglyMeasurable).mp ((hDm m q).sub (hD q)))
        ((memLp_two_iff_integrable_sq_norm ((hDm m q).sub (Lp.memLp (d q))).aestronglyMeasurable).mp
          ((hDm m q).sub (Lp.memLp (d q))))
      intro x
      change ‖DivergenceEnergy.derivative v (U m) x q - D x q‖ ^ 2 ≤
        ‖DivergenceEnergy.derivative v (U m) x q - d q x‖ ^ 2
      by_cases hx : x ∈ K
      · simp only [D, Set.indicator_of_mem hx]
        exact le_rfl
      · have hzero : DivergenceEnergy.derivative v (U m) x q = 0 := by
          unfold DivergenceEnergy.derivative
          rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hUK m q.2 h))]
          rfl
        simp only [D, Set.indicator_of_notMem hx, hzero, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg _
    exact squeeze_zero (fun m => integral_nonneg fun x => sq_nonneg _) hbound hlim

end Euclidean

end Yau.LeafProofs.L03
