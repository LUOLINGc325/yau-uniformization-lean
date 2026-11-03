import Yau.Proofs.F04MassProductError

open Filter Set
open scoped Topology ContDiff Manifold Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

theorem mass_error_cofactor_bound {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ D : ℝ, 0 < D ∧ ∀ (χ : Pt X → ℝ) (C : ℝ),
      (∀ x, 0 < χ x) → (∀ x, gradNormSq X.metric.form χ x ≤ (C * χ x / u x) ^ 2) →
      ∀ R : ℝ, 1 ≤ R → ∀ x t, 0 ≤ t →
        let E := D + C ^ 2 + D ^ 2
        |traceWith (gMat (h t) x) (massProductError u χ R x)| * density ρ x t ≤
          (n : ℝ) * (E * χ x / R ^ 2) := by
  obtain ⟨D, hD, hb⟩ := massProductError_bound X o u hu
  refine ⟨D, hD, ?_⟩
  intro χ C hχ hχgrad R hR x t ht
  have hχx := hχ x
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hE : 0 < D + C ^ 2 + D ^ 2 := by positivity
  by_cases hRx : R ≤ u x
  · have he := hb χ C hχ hχgrad R hR x hRx
    exact flow_signed_cofactor_bound o h U P ρ hloc x t ht (massProductError u χ R x)
      ((D + C ^ 2 + D ^ 2) * χ x / R ^ 2) (by positivity) he.1 he.2
  · rw [massProductError_flat hu.1 hRp x (Or.inl (lt_of_not_ge hRx))]
    simp only [traceWith, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, abs_zero, zero_mul]
    positivity

theorem mass_error_zero_off_shell {n : ℕ} {M : ComplexManifold n}
    {u χ : M.Carrier → ℝ} (hu : SmoothFn u) {R : ℝ} (hR : 0 < R)
    (h : HermitianField M) (x : M.Carrier) (hx : ¬ (R ≤ u x ∧ u x ≤ 2 * R)) :
    traceWith (gMat h x) (massProductError u χ R x) = 0 := by
  have hcase : u x < R ∨ 2 * R < u x := by
    by_cases hh : R ≤ u x
    · exact Or.inr (lt_of_not_ge (fun h => hx ⟨hh, h⟩))
    · exact Or.inl (lt_of_not_ge hh)
  rw [massProductError_flat hu hR x hcase]
  simp only [traceWith, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]

end Yau.F04Proof
