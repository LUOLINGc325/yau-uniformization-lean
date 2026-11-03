import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.Caratheodory

/-! Actual finite positive representations in the cone hull, before any closure. -/

noncomputable section

namespace Yau.NodeProofs.E01Aux

theorem finite_positive_conic_representation
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {S : Set E} {A : E} (hA : A ∈ PointedCone.hull ℝ S) :
    ∃ (m : ℕ) (η : Fin m → E) (α : Fin m → ℝ),
      (∀ i, η i ∈ S ∧ 0 < α i) ∧ ∑ i, α i • η i = A := by
  classical
  obtain ⟨c, hcS, hc0, hcA⟩ := PointedCone.mem_hull_set.mp hA
  let ι := c.support
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, (fun i => (e i).1), (fun i => c (e i).1), ?_, ?_⟩
  · intro i
    exact ⟨hcS (e i).2, lt_of_le_of_ne (hc0 _) (Finsupp.mem_support_iff.mp (e i).2).symm⟩
  · calc
      ∑ i, c (e i).1 • (e i).1 = ∑ j : ι, c j.1 • j.1 :=
        e.sum_comp (fun j : ι => c j.1 • j.1)
      _ = c.sum (fun x r => r • x) := by
        simpa only [ι, Finsupp.sum] using
          (Finset.sum_coe_sort c.support (fun x : E => c x • x))
      _ = A := hcA

theorem cone_hull_functional_nonneg
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {S : Set E} (τ : E →ₗ[ℝ] ℝ) (hτ : ∀ x ∈ S, τ x = 1)
    {A : E} (hA : A ∈ PointedCone.hull ℝ S) : 0 ≤ τ A := by
  obtain ⟨m, η, α, hη, hA⟩ := finite_positive_conic_representation hA
  have hτη (i : Fin m) : τ (η i) = 1 := hτ _ (hη i).1
  rw [← hA, map_sum]
  simp only [map_smul, smul_eq_mul, hτη, mul_one]
  exact Finset.sum_nonneg (fun i _ => (hη i).2.le)

end Yau.NodeProofs.E01Aux
