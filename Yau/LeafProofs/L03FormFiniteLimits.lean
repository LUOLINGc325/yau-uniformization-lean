import Yau.LeafProofs.L03HodgeEnergyApprox

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

def L2FormSpace.toSectionLinear (g : SmoothMetric M) (μ : Measure M.Carrier) (k : ℕ) :
    L2FormSpace g μ k →ₗ[ℝ] RealForm M k where
  toFun := L2FormSpace.toSection
  map_add' := L2FormSpace.toSection_add
  map_smul' := L2FormSpace.toSection_smul

theorem l2RealForm_finset_sum {ι : Type*} (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Finset ι) (A : ι → RealForm M k) (hA : ∀ i ∈ s, L2RealForm g.form μ (A i)) :
    L2RealForm g.form μ (∑ i ∈ s, A i) := (l2FormSubmodule g μ k).sum_mem hA

theorem realizeL2Form_finset_sum {ι : Type*} (g : SmoothMetric M) (μ : Measure M.Carrier)
    (s : Finset ι) (A : ι → RealForm M k) (hA : ∀ i, L2RealForm g.form μ (A i)) :
    realizeL2Form g μ (L2FormSpace.ofSection (∑ i ∈ s, A i) (l2RealForm_finset_sum g μ s A (fun i _ => hA i))) =
      ∑ i ∈ s, realizeL2Form g μ (L2FormSpace.ofSection (A i) (hA i)) := by
  let T := L2FormSpace.toSectionLinear g μ k
  have hc : L2FormSpace.ofSection (∑ i ∈ s, A i) (l2RealForm_finset_sum g μ s A (fun i _ => hA i)) =
      ∑ i ∈ s, L2FormSpace.ofSection (A i) (hA i) := by
    apply L2FormSpace.toSection_injective g μ k
    change T (L2FormSpace.ofSection (∑ i ∈ s, A i)
      (l2RealForm_finset_sum g μ s A (fun i _ => hA i))) =
        T (∑ i ∈ s, L2FormSpace.ofSection (A i) (hA i))
    rw [map_sum]
    rfl
  rw [hc]
  exact map_sum (UniformSpace.Completion.toComplL : L2FormSpace g μ k →L[ℝ] L2FormHilbert g μ k) _ s

theorem formL2DistanceSq_fintype_sum_tendsto {ι : Type*} [Fintype ι]
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (As : ℕ → ι → RealForm M k) (A : ι → RealForm M k)
    (hAs : ∀ m i, L2RealForm g.form μ (As m i)) (hA : ∀ i, L2RealForm g.form μ (A i))
    (ht : ∀ i, Tendsto (fun m => formL2DistanceSq g.form μ (As m i) (A i)) atTop (𝓝 0)) :
    Tendsto (fun m => formL2DistanceSq g.form μ (∑ i, As m i) (∑ i, A i)) atTop (𝓝 0) := by
  classical
  have hi (i : ι) := (tendsto_realizeL2Form_iff g μ
    (fun m => L2FormSpace.ofSection (As m i) (hAs m i)) (L2FormSpace.ofSection (A i) (hA i))).mpr (ht i)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have heq (m : ℕ) : realizeL2Form g μ (L2FormSpace.ofSection (∑ i, As m i)
      (l2RealForm_finset_sum g μ Finset.univ (As m) (fun i _ => hAs m i))) =
        ∑ i, realizeL2Form g μ (L2FormSpace.ofSection (As m i) (hAs m i)) :=
    realizeL2Form_finset_sum g μ Finset.univ (As m) (hAs m)
  have heqA : realizeL2Form g μ (L2FormSpace.ofSection (∑ i, A i)
      (l2RealForm_finset_sum g μ Finset.univ A (fun i _ => hA i))) =
        ∑ i, realizeL2Form g μ (L2FormSpace.ofSection (A i) (hA i)) :=
    realizeL2Form_finset_sum g μ Finset.univ A hA
  have hv : Tendsto
      (fun m => realizeL2Form g μ (L2FormSpace.ofSection (∑ i, As m i)
        (l2RealForm_finset_sum g μ Finset.univ (As m) (fun i _ => hAs m i)))) atTop
      (𝓝 (realizeL2Form g μ (L2FormSpace.ofSection (∑ i, A i)
        (l2RealForm_finset_sum g μ Finset.univ A (fun i _ => hA i))))) := by
    rw [heqA]
    exact hs.congr' (Filter.Eventually.of_forall fun m => (heq m).symm)
  exact (tendsto_realizeL2Form_iff g μ
    (fun m => L2FormSpace.ofSection (∑ i, As m i)
      (l2RealForm_finset_sum g μ Finset.univ (As m) (fun i _ => hAs m i)))
    (L2FormSpace.ofSection (∑ i, A i) (l2RealForm_finset_sum g μ Finset.univ A (fun i _ => hA i)))).mp hv

theorem smoothRealForm_finset_sum {ι : Type*} (s : Finset ι) (A : ι → RealForm M k)
    (hA : ∀ i ∈ s, SmoothRealForm (A i)) : SmoothRealForm (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (smoothRealForm_zero (M := M) (k := k))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact smoothRealForm_add _ _ (hA i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

theorem exteriorRealForm_finset_sum {ι : Type*} (s : Finset ι) (A : ι → RealForm M k)
    (hA : ∀ i ∈ s, SmoothRealForm (A i)) : exteriorRealForm (∑ i ∈ s, A i) = ∑ i ∈ s, exteriorRealForm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      simpa only [zero_smul] using exteriorRealForm_smul (M := M) (k := k) 0 (0 : RealForm M k) smoothRealForm_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, exteriorRealForm_add _ _
        (hA i (Finset.mem_insert_self _ _)) (smoothRealForm_finset_sum s A (fun j hj => hA j (Finset.mem_insert_of_mem hj))),
        ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))]

theorem hodgeLowerRealForm_finset_sum {ι : Type*} (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (s : Finset ι) (A : ι → RealForm M k)
    (hA : ∀ i ∈ s, SmoothRealForm (A i)) :
    hodgeLowerRealForm g.form k (∑ i ∈ s, A i) = ∑ i ∈ s, hodgeLowerRealForm g.form k (A i) := by
  classical
  cases k with
  | zero => simp only [hodgeLowerRealForm, Finset.sum_const_zero]
  | succ j =>
      change codifferentialRealForm g.form (∑ i ∈ s, A i) = ∑ i ∈ s, codifferentialRealForm g.form (A i)
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty, codifferentialRealForm_zero g μ hμ j]
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, codifferentialRealForm_add g μ hμ _ _
            (hA i (Finset.mem_insert_self _ _)) (smoothRealForm_finset_sum s A (fun l hl => hA l (Finset.mem_insert_of_mem hl))),
            ih (fun l hl => hA l (Finset.mem_insert_of_mem hl))]

end Yau.LeafProofs.L03
