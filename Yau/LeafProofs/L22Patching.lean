import Yau.LeafProofs.L22RegularizedMaxRestrict

noncomputable section

open scoped Topology ContDiff
open Set Filter

namespace Yau.LeafProofs.L22Aux

variable {ι X : Type*} [DecidableEq ι] [TopologicalSpace X]

def activeIndices (χ : ι → X → ℝ) (hχ : LocallyFinite (fun i => tsupport (χ i)))
    (x : X) : Finset ι :=
  (hχ.point_finite x).toFinset

@[simp]
theorem mem_activeIndices (χ : ι → X → ℝ)
    (hχ : LocallyFinite (fun i => tsupport (χ i))) (x : X) (i : ι) :
    i ∈ activeIndices χ hχ x ↔ x ∈ tsupport (χ i) := by
  simp only [activeIndices, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

def patchedRegularizedMax (χ : ι → X → ℝ)
    (hχ : LocallyFinite (fun i => tsupport (χ i))) (δ : ι → ℝ)
    (g : ι → X → ℝ) (x : X) : ℝ :=
  regularizedMax (activeIndices χ hχ x) δ (fun i => g i x)

theorem activeIndices_nonempty (χ : ι → X → ℝ)
    (hχ : LocallyFinite (fun i => tsupport (χ i)))
    (hcover : ∀ x, ∃ j, χ j =ᶠ[𝓝 x] (fun _ => 1)) (x : X) :
    (activeIndices χ hχ x).Nonempty := by
  obtain ⟨j, hj⟩ := hcover x
  refine ⟨j, (mem_activeIndices χ hχ x j).mpr ?_⟩
  apply subset_closure
  change χ j x ≠ 0
  rw [hj.eq_of_nhds]
  norm_num

/-- The point-dependent finite expression is locally equal to one fixed
finite regularized maximum. The deletion theorem removes all inactive
branches at once. -/
theorem patchedRegularizedMax_eventuallyEq
    (χ : ι → X → ℝ) (hχ : LocallyFinite (fun i => tsupport (χ i)))
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) (g : ι → X → ℝ) (u : X → ℝ)
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i))
    (hsupp : ∀ i, tsupport (χ i) ⊆ W i)
    (hcover : ∀ x, ∃ j, χ j =ᶠ[𝓝 x] (fun _ => 1))
    (hcore : ∀ i y, y ∈ W i → χ i y = 1 → u y + 6 * δ i < g i y)
    (hzero : ∀ i y, y ∈ W i → χ i y = 0 → g i y < u y - 6 * δ i)
    (x : X) :
    patchedRegularizedMax χ hχ δ g =ᶠ[𝓝 x]
      (fun y => regularizedMax (activeIndices χ hχ x) δ (fun i => g i y)) := by
  obtain ⟨j, hj⟩ := hcover x
  have hsubset : ∀ᶠ y in 𝓝 x, activeIndices χ hχ y ⊆ activeIndices χ hχ x := by
    filter_upwards [hχ.eventually_subset (fun i => isClosed_tsupport (χ i)) x] with y hy i hi
    exact (mem_activeIndices χ hχ x i).mpr (hy ((mem_activeIndices χ hχ y i).mp hi))
  have hWnear : ∀ᶠ y in 𝓝 x, ∀ i ∈ activeIndices χ hχ x, y ∈ W i := by
    apply (activeIndices χ hχ x).eventually_all.mpr
    intro i hi
    exact (hW i).mem_nhds (hsupp i ((mem_activeIndices χ hχ x i).mp hi))
  filter_upwards [hsubset, hWnear, hj] with y hsub hWy hjy
  have hjmem : j ∈ activeIndices χ hχ y := by
    apply (mem_activeIndices χ hχ y j).mpr
    apply subset_closure
    change χ j y ≠ 0
    rw [hjy]
    norm_num
  unfold patchedRegularizedMax
  symm
  apply regularizedMax_restrict _ _ ⟨j, hjmem⟩ hsub δ (fun i => g i y)
    (fun i _ => hδ i)
  intro i hi
  obtain ⟨hix, hiy⟩ := Finset.mem_sdiff.mp hi
  have hzeroi : χ i y = 0 := by
    have hnot : y ∉ tsupport (χ i) := by
      simpa only [mem_activeIndices] using hiy
    exact image_eq_zero_of_notMem_tsupport hnot
  refine ⟨j, hjmem, ?_⟩
  have hilow := hzero i y (hWy i hix) hzeroi
  have hjhigh := hcore j y (hWy j (hsub hjmem)) hjy
  linarith [hδ i, hδ j]

/-- Fine error bounds for the actual locally finite construction. -/
theorem patchedRegularizedMax_error
    (χ : ι → X → ℝ) (hχ : LocallyFinite (fun i => tsupport (χ i)))
    (δ : ι → ℝ) (hδ : ∀ i, 0 < δ i) (g : ι → X → ℝ) (u ε : X → ℝ)
    (W : ι → Set X) (hsupp : ∀ i, tsupport (χ i) ⊆ W i)
    (hcover : ∀ x, ∃ j, χ j =ᶠ[𝓝 x] (fun _ => 1))
    (hcore : ∀ i y, y ∈ W i → χ i y = 1 → u y + 6 * δ i < g i y)
    (hupper : ∀ i y, y ∈ W i → g i y + δ i < u y + ε y)
    (x : X) :
    u x < patchedRegularizedMax χ hχ δ g x ∧
      patchedRegularizedMax χ hχ δ g x < u x + ε x := by
  have hs := activeIndices_nonempty χ hχ hcover x
  obtain ⟨j, hj⟩ := hcover x
  have hjmem : j ∈ activeIndices χ hχ x := by
    apply (mem_activeIndices χ hχ x j).mpr
    apply subset_closure
    change χ j x ≠ 0
    rw [hj.eq_of_nhds]
    norm_num
  constructor
  · have hhigh := hcore j x (hsupp j ((mem_activeIndices χ hχ x j).mp hjmem)) hj.eq_of_nhds
    exact (by linarith [hδ j] : u x < g j x).trans_le
      (regularizedMax_ge _ δ (fun i => g i x) hjmem)
  · let B : ℝ := (activeIndices χ hχ x).sup' hs (fun i => g i x + δ i)
    have hB : B < u x + ε x := by
      apply (Finset.sup'_lt_iff hs).mpr
      intro i hi
      exact hupper i x (hsupp i ((mem_activeIndices χ hχ x i).mp hi))
    apply lt_of_le_of_lt _ hB
    apply regularizedMax_le _ hs δ (fun i => g i x) (fun i _ => hδ i)
    intro i hi
    exact Finset.le_sup' (f := fun i => g i x + δ i) hi

end Yau.LeafProofs.L22Aux
