import spec.CHAIN.HeatConcreteBindings
import Mathlib.Topology.MetricSpace.HausdorffDimension

noncomputable section
open Set Filter MeasureTheory Module
open scoped Topology ENNReal

namespace Yau.Proofs.SmoothExhaustionAux

/-- Simultaneously avoid finitely many differentiable images of smaller
dimension, with an arbitrarily small actual parameter. -/
theorem exists_small_avoiding_finite_images
    {ι : Type*} [Fintype ι]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (A : ι → Type*) [∀ i, NormedAddCommGroup (A i)]
    [∀ i, NormedSpace ℝ (A i)] [∀ i, FiniteDimensional ℝ (A i)]
    (V : ∀ i, Set (A i)) (G : ∀ i, A i → P)
    (hG : ∀ i, DifferentiableOn ℝ (G i) (V i))
    (hDim : ∀ i, Module.finrank ℝ (A i) < Module.finrank ℝ P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : P, ‖θ‖ < ε ∧ ∀ i, θ ∉ G i '' V i := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      letI := h
      exact ⟨0,by simpa only [norm_zero] using hε,fun i => isEmptyElim i⟩
  | inr h =>
      letI := h
      let D := Module.finrank ℝ P
      have hD : 0 < D := lt_of_le_of_lt (Nat.zero_le _) (hDim (Classical.arbitrary ι))
      have hbound (i : ι) : dimH (G i '' V i) ≤ (D-1 : ℕ) := by
        calc
          _ ≤ dimH (V i) := (hG i).dimH_image_le
          _ ≤ dimH (univ : Set (A i)) := dimH_mono (subset_univ _)
          _ = Module.finrank ℝ (A i) := Real.dimH_univ_eq_finrank (A i)
          _ ≤ (D-1 : ℕ) := by exact_mod_cast Nat.le_sub_one_of_lt (hDim i)
      have hdim : dimH (⋃ i, G i '' V i) < Module.finrank ℝ P := by
        rw [dimH_iUnion]
        apply lt_of_le_of_lt (iSup_le hbound)
        exact_mod_cast Nat.sub_lt hD (by norm_num : 0 < 1)
      obtain ⟨θ,hθ,hsmall⟩ := (dense_compl_of_dimH_lt_finrank hdim).exists_mem_open
        Metric.isOpen_ball ⟨0,Metric.mem_ball_self hε⟩
      refine ⟨θ,by simpa only [Metric.mem_ball,dist_zero_right] using hsmall,?_⟩
      intro i hi
      exact hθ (mem_iUnion_of_mem i hi)

theorem continuous_dual_finrank {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem affine_graph_parameter_dimension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {N : ℕ} (i : Fin N) :
    Module.finrank ℝ (E × ({j : Fin N // j ≠ i} → ((E →L[ℝ] ℝ) × ℝ))) <
      Module.finrank ℝ (Fin N → ((E →L[ℝ] ℝ) × ℝ)) := by
  have hcard : Fintype.card {j : Fin N // j ≠ i} = N-1 := by
    simpa only [Fintype.card_fin,Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun j : Fin N => j=i)
  simp only [Module.finrank_prod, Module.finrank_pi_fintype, continuous_dual_finrank,
    Module.finrank_self, Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fin,hcard,Nat.cast_id]
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  calc
    _ < (Module.finrank ℝ E+1)+(N-1)*(Module.finrank ℝ E+1) :=
      Nat.add_lt_add_right (Nat.lt_succ_self _) _
    _ = N*(Module.finrank ℝ E+1) := by
      rw [Nat.add_comm, ← Nat.succ_mul]
      congr 1
      omega

end Yau.Proofs.SmoothExhaustionAux
