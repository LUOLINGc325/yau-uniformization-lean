import Yau.Proofs.D02CotangentBox

/-! Closed restrictions, extrema and zero fibres in the actual cotangent atlas. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {n : ℕ} {M : ComplexManifold n}

/-- Continuous functions in the actual induced charts have compact images. -/
theorem cotangentCompact_image {E : Type*} [TopologicalSpace E]
    {L : Set (CotangentPoint M)} (hL : CotangentCompact L)
    {F : CotangentPoint M → E}
    (hF : ∀ x, ContinuousOn (fun p => F (cotangentChartInv x p)) (cotangentTarget x)) :
    IsCompact (F '' L) := by
  obtain ⟨r, x, C, hC, rfl⟩ := hL
  rw [Set.image_iUnion]
  apply isCompact_iUnion
  intro i
  simpa only [Set.image_image, Function.comp_def] using
    (hC i).1.image_of_continuousOn ((hF (x i)).mono (hC i).2)

/-- Closed restrictions retain the exact finite chart representation. -/
theorem cotangentCompact_inter_preimage {E : Type*} [TopologicalSpace E]
    {L : Set (CotangentPoint M)} (hL : CotangentCompact L)
    {F : CotangentPoint M → E}
    (hF : ∀ x, ContinuousOn (fun p => F (cotangentChartInv x p)) (cotangentTarget x))
    {S : Set E} (hS : IsClosed S) :
    CotangentCompact (L ∩ F ⁻¹' S) := by
  obtain ⟨r, x, C, hC, hL⟩ := hL
  let C' : Fin r → Set (CotangentCoord n) :=
    fun i => C i ∩ (fun p => F (cotangentChartInv (x i) p)) ⁻¹' S
  refine ⟨r, x, C', fun i => ⟨?_, fun p hp => (hC i).2 hp.1⟩, ?_⟩
  · exact (hC i).1.of_isClosed_subset
      (((hF (x i)).mono (hC i).2).preimage_isClosed_of_isClosed (hC i).1.isClosed hS)
      Set.inter_subset_left
  · ext y
    constructor
    · rintro ⟨hyL, hyS⟩
      rw [hL] at hyL
      obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hyL
      exact Set.mem_iUnion.mpr ⟨i, p, ⟨hp, hyS⟩, rfl⟩
    · intro hy
      obtain ⟨i, p, hp, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨hL ▸ Set.mem_iUnion.mpr ⟨i, p, hp.1, rfl⟩, hp.2⟩

/-- Positive functions have one positive lower bound on an intrinsic compact. -/
theorem cotangentCompact_pos_lower_bound {L : Set (CotangentPoint M)}
    (hL : CotangentCompact L) {F : CotangentPoint M → ℝ}
    (hF : ∀ x, ContinuousOn (fun p => F (cotangentChartInv x p)) (cotangentTarget x))
    (hpos : ∀ y ∈ L, 0 < F y) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ L, c ≤ F y := by
  obtain ⟨c, hc, hbound⟩ := (cotangentCompact_image hL hF).exists_forall_le'
    continuous_id.continuousOn (a := 0) (by
      rintro a ⟨y, hy, rfl⟩
      exact hpos y hy)
  exact ⟨c, hc, fun y hy => hbound (F y) (Set.mem_image_of_mem F hy)⟩

theorem dualNormMat_eq_zero_iff {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (ξ : ComplexVector n) : dualNormMat H ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro hzero
    by_contra hξ
    have hξ' : WithLp.ofLp ξ ≠ 0 := by
      intro he
      apply hξ
      ext i
      exact congrArg (fun v : Fin n → ℂ => v i) he
    have hp := (Complex.pos_iff.mp (hH.inv.transpose.dotProduct_mulVec_pos hξ')).1
    exact (ne_of_gt hp) hzero
  · rintro rfl
    simp [dualNormMat]

theorem dualNorm_eq_zero_iff (g : HermitianField M) (x : M.Carrier) (ξ : Covector n) :
    dualNorm g x ξ = 0 ↔ ξ = 0 := by
  rw [dualNorm, dualNormMat_eq_zero_iff (gMat_posDef g x)]
  constructor
  · intro hξ
    ext v
    have h := covector_apply_chartVec x x ξ (tangentCoords x x v)
    have he : chartVec x x (tangentCoords x x v) = v :=
      Yau.Blueprint.V03Proof.chartVec_tangentCoords x x (mem_extChartAt_source x) v
    change ξ v = 0
    calc
      ξ v = ξ (chartVec x x (tangentCoords x x v)) := congrArg ξ he.symm
      _ = _ := h
      _ = 0 := by simp [hξ]
  · rintro rfl
    ext i
    rfl

/-- Negative thresholds produce the empty set, with no omitted edge case. -/
theorem cotangentBox_eq_empty_of_neg (g : HermitianField M) (K : Set M.Carrier)
    {R : ℝ} (hR : R < 0) :
    {y : CotangentPoint M | InCotangentCompact g K R y.1 y.2} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact (not_le_of_gt hR) ((dualNorm_nonneg g y.1 y.2).trans hy.2)

/-- The zero threshold is exactly the zero section over the base set. -/
theorem cotangentBox_zero (g : HermitianField M) (K : Set M.Carrier) :
    {y : CotangentPoint M | InCotangentCompact g K 0 y.1 y.2} =
      {y : CotangentPoint M | y.1 ∈ K ∧ y.2 = 0} := by
  ext y
  change (y.1 ∈ K ∧ dualNorm g y.1 y.2 ≤ 0) ↔ (y.1 ∈ K ∧ y.2 = 0)
  constructor
  · rintro ⟨hy, hq⟩
    exact ⟨hy, (dualNorm_eq_zero_iff g y.1 y.2).mp
      (le_antisymm hq (dualNorm_nonneg g y.1 y.2))⟩
  · rintro ⟨hy, hξ⟩
    exact ⟨hy, ((dualNorm_eq_zero_iff g y.1 y.2).mpr hξ).le⟩

end Yau.NodeProofs.D02Aux
