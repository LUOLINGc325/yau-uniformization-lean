import Yau.LeafProofs.L03GraphClosure

open MeasureTheory Filter Module
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

/-- Multiplying a finite scalar system by a smooth cutoff gives the same
cutoff coefficients plus its exact first-order commutator. -/
theorem firstOrderSystemApply_cutoff {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype α] [Fintype ι]
    (v : ι → E) (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (χ : E → ℝ) (u : E → α → ℝ)
    (hχ : Differentiable ℝ χ) (hu : ∀ c, Differentiable ℝ (fun x => u x c))
    (x : E) (r : β) :
    firstOrderSystemApply v a b (fun x c => χ x * u x c) x r =
      firstOrderSystemApply v (fun r c i x => χ x * a r c i x)
        (fun r c x => χ x * b r c x) u x r +
      ∑ c, ∑ i, a r c i x * fderiv ℝ χ x (v i) * u x c := by
  classical
  have hd (c : α) (i : ι) :
      fderiv ℝ (fun y => χ y * u y c) x (v i) =
        χ x * fderiv ℝ (fun y => u y c) x (v i) + u x c * fderiv ℝ χ x (v i) := by
    rw [fderiv_fun_mul (hχ x) (hu c x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [firstOrderSystemApply, hd]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  calc
    _ = (∑ i, ((χ x * a r c i x) * fderiv ℝ (fun y => u y c) x (v i) +
        a r c i x * fderiv ℝ χ x (v i) * u x c)) + (χ x * b r c x) * u x c := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        ring
      · ring
    _ = _ := by rw [Finset.sum_add_distrib]; ring

/-- A fixed bounded measurable scalar multiplier preserves strong L²
convergence expressed by the integral of the actual squared norm. -/
theorem integral_sq_tendsto_zero_bounded_mul {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (f : ℕ → E → ℝ) (hf : ∀ j, MemLp (f j) 2 ν)
    (ht : Tendsto (fun j => ∫ x, ‖f j x‖ ^ 2 ∂ν) atTop (𝓝 0))
    (c : E → ℝ) (hc : AEStronglyMeasurable c ν) (C : ℝ) (hC : 0 ≤ C)
    (hcC : ∀ x, ‖c x‖ ≤ C) :
    (∀ j, MemLp (fun x => c x * f j x) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖c x * f j x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  have hm (j : ℕ) : MemLp (fun x => c x * f j x) 2 ν := by
    apply (hf j).of_le_mul (c := C) (hc.mul (hf j).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change ‖c x * f j x‖ ≤ C * ‖f j x‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hcC x) (norm_nonneg _)
  refine ⟨hm, ?_⟩
  have hb (j : ℕ) : (∫ x, ‖c x * f j x‖ ^ 2 ∂ν) ≤ C ^ 2 * ∫ x, ‖f j x‖ ^ 2 ∂ν := by
    have hi := (memLp_two_iff_integrable_sq_norm (hf j).aestronglyMeasurable).mp (hf j)
    have hci := (memLp_two_iff_integrable_sq_norm (hm j).aestronglyMeasurable).mp (hm j)
    calc
      _ ≤ ∫ x, C ^ 2 * ‖f j x‖ ^ 2 ∂ν := integral_mono hci (hi.const_mul _) (fun x => by
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          ((sq_le_sq₀ (norm_nonneg _) hC).mpr (hcC x)) (sq_nonneg _))
      _ = _ := integral_const_mul _ _
  exact squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _) hb (by
    simpa only [mul_zero] using ht.const_mul (C ^ 2))

/-- A finite sum of strong L² errors is again a strong L² error. -/
theorem integral_sq_tendsto_zero_fintype_sum {E F ι : Type*}
    [MeasurableSpace E] [NormedAddCommGroup F] [Fintype ι]
    (ν : Measure E) (f : ℕ → E → ι → F)
    (hf : ∀ j i, MemLp (fun x => f j x i) 2 ν)
    (ht : ∀ i, Tendsto (fun j => ∫ x, ‖f j x i‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    (∀ j, MemLp (fun x => ∑ i, f j x i) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖∑ i, f j x i‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  classical
  have hm (j : ℕ) : MemLp (fun x => ∑ i, f j x i) 2 ν := by
    simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun i _ => hf j i)
  refine ⟨hm, ?_⟩
  have hi (j : ℕ) (i : ι) : Integrable (fun x => ‖f j x i‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (hf j i).aestronglyMeasurable).mp (hf j i)
  have hb (j : ℕ) : (∫ x, ‖∑ i, f j x i‖ ^ 2 ∂ν) ≤
      (Fintype.card ι : ℝ) * ∑ i, ∫ x, ‖f j x i‖ ^ 2 ∂ν := by
    have hsi := (memLp_two_iff_integrable_sq_norm (hm j).aestronglyMeasurable).mp (hm j)
    calc
      _ ≤ ∫ x, (Fintype.card ι : ℝ) * ∑ i, ‖f j x i‖ ^ 2 ∂ν :=
        integral_mono hsi ((integrable_finsetSum Finset.univ (fun i _ => hi j i)).const_mul _) (fun x => by
          have h := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ => norm_nonneg (f j x i))).mpr
            (norm_sum_le Finset.univ (fun i => f j x i))
          exact h.trans (by simpa only [Finset.card_univ] using
            sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f j x i‖)))
      _ = _ := by rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi j i)]
  exact squeeze_zero (fun j => integral_nonneg fun x => sq_nonneg _) hb (by
    simpa only [Finset.sum_const_zero, mul_zero] using
      (tendsto_finsetSum Finset.univ (fun i _ => ht i)).const_mul (Fintype.card ι : ℝ))

/-- The same cutoff that extends the weak equation also makes its smooth
approximants chart supported. Only value errors enter the commutator. -/
theorem firstOrderSystemApply_cutoff_graph_tendsto {E α β ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [Fintype α] [Fintype ι]
    (ν : Measure E) (v : ι → E)
    (a : β → α → ι → E → ℝ) (b : β → α → E → ℝ)
    (χ : E → ℝ) (hχ : Differentiable ℝ χ) (hχm : AEStronglyMeasurable χ ν)
    (Cχ : ℝ) (hCχ : 0 ≤ Cχ) (hχC : ∀ x, ‖χ x‖ ≤ Cχ)
    (u : E → α → ℝ) (w : E → β → ℝ) (U : ℕ → E → α → ℝ)
    (hU : ∀ j c, Differentiable ℝ (fun x => U j x c))
    (hu : ∀ c, MemLp (fun x => u x c) 2 ν)
    (hUm : ∀ j c, MemLp (fun x => U j x c) 2 ν)
    (hw : ∀ r, MemLp (fun x => w x r) 2 ν)
    (htu : ∀ c, Tendsto (fun j => ∫ x, ‖U j x c - u x c‖ ^ 2 ∂ν) atTop (𝓝 0))
    (hPm : ∀ j r, MemLp (fun x => firstOrderSystemApply v
      (fun r c i x => χ x * a r c i x) (fun r c x => χ x * b r c x) (U j) x r) 2 ν)
    (htP : ∀ r, Tendsto (fun j => ∫ x, ‖firstOrderSystemApply v
      (fun r c i x => χ x * a r c i x) (fun r c x => χ x * b r c x) (U j) x r - w x r‖ ^ 2 ∂ν)
        atTop (𝓝 0))
    (hχu : ∀ x c, χ x * u x c = u x c)
    (hχdu : ∀ x c i, fderiv ℝ χ x (v i) * u x c = 0)
    (hm : ∀ r c i, AEStronglyMeasurable (fun x => a r c i x * fderiv ℝ χ x (v i)) ν)
    (C : β → α → ι → ℝ) (hC : ∀ r c i, 0 ≤ C r c i)
    (hbound : ∀ r c i x, ‖a r c i x * fderiv ℝ χ x (v i)‖ ≤ C r c i) :
    (∀ c, Tendsto (fun j => ∫ x, ‖χ x * U j x c - u x c‖ ^ 2 ∂ν) atTop (𝓝 0)) ∧
      ∀ r, (∀ j, MemLp (fun x =>
          firstOrderSystemApply v a b (fun x c => χ x * U j x c) x r - w x r) 2 ν) ∧
        Tendsto (fun j => ∫ x,
          ‖firstOrderSystemApply v a b (fun x c => χ x * U j x c) x r - w x r‖ ^ 2 ∂ν)
          atTop (𝓝 0) := by
  classical
  have he (j : ℕ) (c : α) : MemLp (fun x => U j x c - u x c) 2 ν := (hUm j c).sub (hu c)
  refine ⟨?_, ?_⟩
  · intro c
    have h := (integral_sq_tendsto_zero_bounded_mul ν (fun j x => U j x c - u x c)
      (fun j => he j c) (htu c) χ hχm Cχ hCχ hχC).2
    convert h using 1
    funext j
    congr 1
    funext x
    rw [mul_sub, hχu]
  intro r
  let T : ℕ → E → Unit ⊕ (α × ι) → ℝ := fun j x s => match s with
    | .inl _ => firstOrderSystemApply v
        (fun r c i x => χ x * a r c i x) (fun r c x => χ x * b r c x) (U j) x r - w x r
    | .inr (c, i) => (a r c i x * fderiv ℝ χ x (v i)) * (U j x c - u x c)
  have hcross (c : α) (i : ι) := integral_sq_tendsto_zero_bounded_mul ν
    (fun j x => U j x c - u x c) (fun j => he j c) (htu c)
    (fun x => a r c i x * fderiv ℝ χ x (v i)) (hm r c i)
    (C r c i) (hC r c i) (hbound r c i)
  have hT (j : ℕ) (s : Unit ⊕ (α × ι)) : MemLp (fun x => T j x s) 2 ν := by
    rcases s with t | ⟨c, i⟩
    · exact (hPm j r).sub (hw r)
    · exact (hcross c i).1 j
  have htT (s : Unit ⊕ (α × ι)) : Tendsto
      (fun j => ∫ x, ‖T j x s‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    rcases s with t | ⟨c, i⟩
    · exact htP r
    · exact (hcross c i).2
  have hId (j : ℕ) (x : E) :
      firstOrderSystemApply v a b (fun x c => χ x * U j x c) x r - w x r = ∑ s, T j x s := by
    rw [firstOrderSystemApply_cutoff v a b χ (U j) hχ (hU j)]
    have hs : (∑ s, T j x s) =
        firstOrderSystemApply v (fun r c i x => χ x * a r c i x)
          (fun r c x => χ x * b r c x) (U j) x r - w x r +
          ∑ c, ∑ i, (a r c i x * fderiv ℝ χ x (v i)) * (U j x c - u x c) := by
      simp [T, Fintype.sum_sum_type, Fintype.sum_prod_type]
    rw [hs]
    have hh : (∑ c, ∑ i, (a r c i x * fderiv ℝ χ x (v i)) * (U j x c - u x c)) =
        ∑ c, ∑ i, a r c i x * fderiv ℝ χ x (v i) * U j x c := by
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_sub, mul_assoc, hχdu, mul_zero, sub_zero]
    rw [hh]
    ring
  have hs := integral_sq_tendsto_zero_fintype_sum ν T hT htT
  simpa only [← hId] using hs

/-- Finite basis coordinates detect strong L² convergence in the actual
finite-dimensional model fibre. -/
theorem integral_sq_tendsto_zero_of_basis_coordinates {E F α : Type*}
    [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype α] (ν : Measure E) (b : Basis α ℝ F) (f : ℕ → E → F)
    (hf : ∀ j c, MemLp (fun x => b.repr (f j x) c) 2 ν)
    (ht : ∀ c, Tendsto (fun j => ∫ x, ‖b.repr (f j x) c‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    (∀ j, MemLp (f j) 2 ν) ∧
      Tendsto (fun j => ∫ x, ‖f j x‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  classical
  let T : ℕ → E → α → F := fun j x c => b.repr (f j x) c • b c
  have hT (j : ℕ) (c : α) : MemLp (fun x => T j x c) 2 ν := by
    exact (ContinuousLinearMap.toSpanSingleton ℝ (b c)).comp_memLp' (hf j c)
  have htT (c : α) : Tendsto (fun j => ∫ x, ‖T j x c‖ ^ 2 ∂ν) atTop (𝓝 0) := by
    have heq (j : ℕ) : (∫ x, ‖T j x c‖ ^ 2 ∂ν) =
        ‖b c‖ ^ 2 * ∫ x, ‖b.repr (f j x) c‖ ^ 2 ∂ν := by
      simp only [T, norm_smul, mul_pow]
      rw [show (fun x => ‖b.repr (f j x) c‖ ^ 2 * ‖b c‖ ^ 2) =
        (fun x => ‖b c‖ ^ 2 * ‖b.repr (f j x) c‖ ^ 2) by funext x; ring,
        integral_const_mul]
    simpa only [heq, mul_zero] using (ht c).const_mul (‖b c‖ ^ 2)
  simpa only [T, b.sum_repr] using integral_sq_tendsto_zero_fintype_sum ν T hT htT

end Yau.LeafProofs.L03
