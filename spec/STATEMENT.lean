import Yau.Geometry.Basic
import Yau.Proofs.MainEndpoint
import Yau.Witness.Cigar

/-!
Formal statement of `thm:uniformization` / Theorem 1.1 in
`spec/paper/build/sections/introduction.tex` (lines 8–13).
The geometric definitions come from the concrete Mathlib-backed base.
-/

namespace Yau

/-- Theorem 1.1: a connected noncompact complex manifold of complex dimension
`n ≥ 1` admitting a smooth complete Kähler metric with strictly positive
holomorphic bisectional curvature is biholomorphic to `ℂⁿ`.

`KahlerManifold n` packages these hypotheses; the pointwise curvature condition
is `Rm(u,v,v,u) + Rm(u,Jv,Jv,u) > 0`, computed from the metric's
Levi-Civita symbols. -/
theorem main {n : ℕ} (hn : 1 ≤ n) (X : KahlerManifold n) :
    BiholomorphicToComplexEuclidean X.manifold := by
  exact Yau.NodeProofs.main_endpoint hn X

/- The ambient model ℂⁿ is a genuine charted connected noncompact manifold and
   is biholomorphic to itself.  This checks the conclusion model independently
   of the theorem's positive-curvature hypothesis. -/
theorem complex_euclidean_model_biholomorphic (n : ℕ) (hn : 1 ≤ n) :
    BiholomorphicToComplexEuclidean (ComplexEuclideanManifold n hn) := by
  let e := Diffeomorph.refl (ComplexModel n)
    (ComplexEuclideanManifold n hn).Carrier ⊤
  refine ⟨⟨hn, e, ?_, ?_⟩⟩
  · constructor
    · exact e.contMDiff
    · intro x a v
      change mfderiv (ComplexModel n) (ComplexModel n)
          (@id ((ComplexEuclideanManifold n hn).Carrier)) x (a • v) =
        a • mfderiv (ComplexModel n) (ComplexModel n)
          (@id ((ComplexEuclideanManifold n hn).Carrier)) x v
      rw [mfderiv_id]
      rfl
  · constructor
    · exact e.symm.contMDiff
    · intro x a v
      change mfderiv (ComplexModel n) (ComplexModel n)
          (@id ((ComplexEuclideanManifold n hn).Carrier)) x (a • v) =
        a • mfderiv (ComplexModel n) (ComplexModel n)
          (@id ((ComplexEuclideanManifold n hn).Carrier)) x v
      rw [mfderiv_id]
      rfl

/-- The complete positively curved cigar witnesses that the hypotheses of
Theorem 1.1 are inhabited in complex dimension one. -/
theorem main_nonvacuous : Nonempty (KahlerManifold 1) :=
  kahlerManifold_one_nonempty

end Yau
