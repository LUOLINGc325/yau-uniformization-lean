import Yau.LeafProofs.L03ChartApprox

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

def firstOrderSystemValueFromJet {E α β ι : Type*} [Fintype α] [Fintype ι]
    (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (u : E → α → ℝ) (D : E → ι × α → ℝ) (x : E) (r : β) : ℝ :=
  ∑ c, ((∑ i, a r c i x * D x (i, c)) + b r c x * u x c)

/-- Strong limits of genuine first derivatives give strong limits of
every bounded finite first-order system. Only the smooth approximants
are differentiated; the limiting value and derivative data are raw L². -/
theorem firstOrderSystemApply_gradient_limits_tendsto {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [Fintype α] [Fintype ι]
    (ν : Measure E) (v : ι → E) (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (ha : ∀ r c i, AEStronglyMeasurable (a r c i) ν)
    (hb : ∀ r c, AEStronglyMeasurable (b r c) ν)
    (A : β → α → ι → ℝ) (hA : ∀ r c i x, ‖a r c i x‖ ≤ A r c i)
    (B : β → α → ℝ) (hB : ∀ r c x, ‖b r c x‖ ≤ B r c)
    (U : ℕ → E → α → ℝ) (u : E → α → ℝ) (D : E → ι × α → ℝ)
    (hU : ∀ m c, MemLp (fun x => U m x c) 2 ν)
    (hu : ∀ c, MemLp (fun x => u x c) 2 ν)
    (hUd : ∀ m i c, MemLp (fun x => fderiv ℝ (fun y => U m y c) x (v i)) 2 ν)
    (hD : ∀ q, MemLp (fun x => D x q) 2 ν)
    (hUt : ∀ c, Tendsto (fun m => ∫ x, ‖U m x c - u x c‖ ^ 2 ∂ν) atTop (𝓝 0))
    (hDt : ∀ i c, Tendsto (fun m => ∫ x,
      ‖fderiv ℝ (fun y => U m y c) x (v i) - D x (i, c)‖ ^ 2 ∂ν) atTop (𝓝 0)) (r : β) :
    (∀ m, MemLp (fun x => firstOrderSystemApply v a b (U m) x r) 2 ν) ∧
      MemLp (fun x => firstOrderSystemValueFromJet a b u D x r) 2 ν ∧
      Tendsto (fun m => ∫ x, ‖firstOrderSystemApply v a b (U m) x r -
        firstOrderSystemValueFromJet a b u D x r‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  classical
  have hA0 (c : α) (i : ι) : 0 ≤ A r c i := (norm_nonneg _).trans (hA r c i 0)
  have hB0 (c : α) : 0 ≤ B r c := (norm_nonneg _).trans (hB r c 0)
  have hmul (f : E → ℝ) (hf : MemLp f 2 ν) (q : E → ℝ)
      (hq : AEStronglyMeasurable q ν) (C : ℝ) (hbound : ∀ x, ‖q x‖ ≤ C) :
      MemLp (fun x => q x * f x) 2 ν := by
    apply hf.of_le_mul (c := C) (hq.mul hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change ‖q x * f x‖ ≤ C * ‖f x‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
  have hPm (m : ℕ) : MemLp (fun x => firstOrderSystemApply v a b (U m) x r) 2 ν := by
    apply memLp_finsetSum
    intro c _
    exact (memLp_finsetSum Finset.univ (fun i _ => hmul _ (hUd m i c) _ (ha r c i) _ (hA r c i))).add
      (hmul _ (hU m c) _ (hb r c) _ (hB r c))
  have hWm : MemLp (fun x => firstOrderSystemValueFromJet a b u D x r) 2 ν := by
    apply memLp_finsetSum
    intro c _
    exact (memLp_finsetSum Finset.univ (fun i _ => hmul _ (hD (i, c)) _ (ha r c i) _ (hA r c i))).add
      (hmul _ (hu c) _ (hb r c) _ (hB r c))
  let γ := α × (ι ⊕ Unit)
  let R : ℕ → E → γ → ℝ := fun m x s => match s.2 with
    | .inl i => a r s.1 i x * (fderiv ℝ (fun y => U m y s.1) x (v i) - D x (i, s.1))
    | .inr _ => b r s.1 x * (U m x s.1 - u x s.1)
  have hRA (c : α) (i : ι) := integral_sq_tendsto_zero_bounded_mul ν
    (fun m x => fderiv ℝ (fun y => U m y c) x (v i) - D x (i, c))
    (fun m => (hUd m i c).sub (hD (i, c))) (hDt i c) (a r c i) (ha r c i) (A r c i) (hA0 c i) (hA r c i)
  have hRB (c : α) := integral_sq_tendsto_zero_bounded_mul ν (fun m x => U m x c - u x c)
    (fun m => (hU m c).sub (hu c)) (hUt c) (b r c) (hb r c) (B r c) (hB0 c) (hB r c)
  have hRm (m : ℕ) (s : γ) : MemLp (fun x => R m x s) 2 ν := by
    rcases s with ⟨c, i | t⟩
    · exact (hRA c i).1 m
    · exact (hRB c).1 m
  have hRt (s : γ) : Tendsto (fun m => ∫ x, ‖R m x s‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    rcases s with ⟨c, i | t⟩
    · exact (hRA c i).2
    · exact (hRB c).2
  have hsum := integral_sq_tendsto_zero_fintype_sum ν R hRm hRt
  have heq (m : ℕ) (x : E) : firstOrderSystemApply v a b (U m) x r -
      firstOrderSystemValueFromJet a b u D x r = ∑ s, R m x s := by
    simp only [firstOrderSystemApply, firstOrderSystemValueFromJet, γ,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_unique, R,
      mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  exact ⟨hPm, hWm, by simpa only [heq] using hsum.2⟩

end Yau.LeafProofs.L03
