import Yau.Proofs.F01CompactUniformSubsequence

/-! Actual first derivative bounds on a convex compact domain supply
equicontinuity and hence an actual uniformly convergent subsequence. -/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction NNReal
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem convex_derivative_bound_lipschitz
    {S : Set E} (hS : Convex ℝ S) (f : E → F) (f' : E → E →L[ℝ] F) (C : ℝ≥0)
    (hf : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x)
    (hbound : ∀ x ∈ S, ‖f' x‖ ≤ C) :
    LipschitzWith C (fun x : S => f x) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simpa only [dist_eq_norm, Subtype.dist_eq] using
    Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hbound hS y.property x.property

theorem compact_uniform_subsequence_of_derivative_bounds [ProperSpace F]
    {S : Set E} (hS : Convex ℝ S) (hcompact : IsCompact S)
    (f : ℕ → E → F) (f' : ℕ → E → E →L[ℝ] F) (C : ℝ≥0) {B : ℝ}
    (hf : ∀ m x, x ∈ S → HasFDerivWithinAt (f m) (f' m x) S x)
    (hderiv : ∀ m x, x ∈ S → ‖f' m x‖ ≤ C)
    (hvalue : ∀ m x, x ∈ S → ‖f m x‖ ≤ B) :
    ∃ g : S → F, Continuous g ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      TendstoUniformly (fun (m : ℕ) (x : S) => f (σ m) x) g atTop := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  have hc (m : ℕ) : ContinuousOn (f m) S := fun x hx => (hf m x hx).continuousWithinAt
  let u : ℕ → S →ᵇ F := fun m => BoundedContinuousFunction.mkOfCompact
    ⟨(fun x : S => f m x), (hc m).restrict⟩
  have hLip (m : ℕ) : LipschitzWith C (fun x : S => u m x) :=
    convex_derivative_bound_lipschitz hS (f m) (f' m) C (hf m) (hderiv m)
  have hEqui : Equicontinuous (fun m x => u m x) :=
    (LipschitzWith.uniformEquicontinuous (fun m x => u m x) C hLip).equicontinuous
  obtain ⟨v, σ, hσ, hconv⟩ := compact_uniform_subsequence_of_equicontinuous u hEqui
    (fun m x => hvalue m x x.property)
  exact ⟨v, v.continuous, σ, hσ, hconv⟩

end Yau.NodeProofs.F01Aux
