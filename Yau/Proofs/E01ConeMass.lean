import Yau.Proofs.E01FiniteCone

/-! The exact mass normalization of a finite cone over an affine base. -/

noncomputable section

namespace Yau.NodeProofs.E01Aux

theorem cone_hull_normalized_representation
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (hS : S.Nonempty) (τ : E →ₗ[ℝ] ℝ)
    (hτ : ∀ x ∈ S, τ x = 1) {A : E} (hA : A ∈ PointedCone.hull ℝ S) :
    ∃ B ∈ convexHull ℝ S, A = (τ A) • B := by
  classical
  obtain ⟨m, η, α, hη, hrep⟩ := finite_positive_conic_representation hA
  have hτη (i : Fin m) : τ (η i) = 1 := hτ _ (hη i).1
  have hmass : τ A = ∑ i, α i := by
    rw [← hrep, map_sum]
    simp only [map_smul, smul_eq_mul, hτη, mul_one]
  have hnonneg : 0 ≤ τ A := cone_hull_functional_nonneg τ hτ hA
  by_cases hz : τ A = 0
  · have hsum : ∑ i, α i = 0 := hmass.symm.trans hz
    have hα0 (i : Fin m) : α i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hη j).2.le)).mp hsum i
        (Finset.mem_univ i)
    have hA0 : A = 0 := by
      rw [← hrep]
      simp only [hα0, zero_smul, Finset.sum_const_zero]
    obtain ⟨B, hB⟩ := hS
    exact ⟨B, subset_convexHull ℝ S hB, by simpa only [hz, zero_smul] using hA0⟩
  · have hpos : 0 < τ A := lt_of_le_of_ne hnonneg (Ne.symm hz)
    let B : E := ∑ i, (α i / τ A) • η i
    have htotal : ∑ i, α i / τ A = 1 := by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← hmass, mul_inv_cancel₀ hpos.ne']
    have hB : B ∈ convexHull ℝ S :=
      (convex_convexHull ℝ S).sum_mem
        (fun i _ => div_nonneg (hη i).2.le hpos.le) htotal
        (fun i _ => subset_convexHull ℝ S (hη i).1)
    have heq : (τ A) • B = A := by
      dsimp only [B]
      rw [Finset.smul_sum]
      calc
        ∑ i, (τ A) • ((α i / τ A) • η i) = ∑ i, α i • η i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_smul]
          congr 1
          field_simp [hpos.ne']
        _ = A := hrep
    exact ⟨B, hB, heq.symm⟩

theorem convexHull_functional_eq_one
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} (τ : E →ₗ[ℝ] ℝ) (hτ : ∀ x ∈ S, τ x = 1)
    {B : E} (hB : B ∈ convexHull ℝ S) : τ B = 1 := by
  have hcv : Convex ℝ {x : E | τ x = 1} := by
    intro x hx y hy a b _ _ hab
    change τ (a • x + b • y) = 1
    rw [map_add, map_smul, map_smul, hx, hy]
    simpa only [smul_eq_mul, mul_one] using hab
  exact convexHull_min (fun x hx => hτ x hx) hcv hB

theorem nonnegative_smul_convexHull_mem_cone
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {B : E} (hB : B ∈ convexHull ℝ S)
    {r : ℝ} (hr : 0 ≤ r) : r • B ∈ PointedCone.hull ℝ S := by
  have hBC : B ∈ PointedCone.hull ℝ S :=
    convexHull_min PointedCone.subset_hull (PointedCone.hull ℝ S).convex hB
  exact (PointedCone.hull ℝ S).smul_mem hr hBC

end Yau.NodeProofs.E01Aux
