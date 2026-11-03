import Yau.Proofs.P03Frames

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The scalar interpolation clause separates any two distinct actual points.
This records a consequence used in the later finite-dimensional selection. -/
theorem scalar_jets_separate_points
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k)
    {x y : M.Carrier} (hxy : x ≠ y) :
    ∃ f : M.Carrier → ℂ, IsHolomorphicFn f ∧ f x = 0 ∧ f y = 1 := by
  classical
  let P : M.Carrier → MvPolynomial (Fin n) ℂ := fun p =>
    MvPolynomial.C (if p = x then 0 else 1)
  obtain ⟨f, hf, hjet⟩ := hjets {x, y} 0 P
  refine ⟨f, hf, ?_, ?_⟩
  · simpa [P] using jetAgreeFn_value (hjet x (by simp))
  · simpa [P, Ne.symm hxy] using jetAgreeFn_value (hjet y (by simp))

/-- The field interpolation clause makes actual fibre evaluation surjective.
The prescribed coefficients are transported through the inverse-chart
differential, so the output is equality in the intrinsic tangent fibre. -/
theorem field_jets_evaluation_surjective
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → Fin n → MvPolynomial (Fin n) ℂ),
      ∃ V : VectorField M, IsHolomorphicField V ∧
        ∀ p ∈ pts, JetAgreeField V p (Pj p) k)
    (p : M.Carrier) (v : TangentVector M p) :
    ∃ V : VectorField M, IsHolomorphicField V ∧ V p = v := by
  classical
  let P : M.Carrier → Fin n → MvPolynomial (Fin n) ℂ := fun _ i =>
    MvPolynomial.C (tangentCoords p p v i)
  obtain ⟨V, hV, hjet⟩ := hjets {p} 0 P
  refine ⟨V, hV, ?_⟩
  have heq : tangentCoords p p (V p) = tangentCoords p p v := by
    simpa [P] using jetAgreeField_value (hjet p (by simp))
  have h := congrArg (chartVec p p) heq
  simpa only [chartVec_tangentCoords p p (mem_extChartAt_source p)] using h

theorem chart_frame_span (p : M.Carrier) :
    Submodule.span ℂ (Set.range fun i : Fin n => chartVec p p (stdVec i)) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro v
  have he : (∑ i : Fin n, tangentCoords p p v i • stdVec i) = tangentCoords p p v := by
    ext j
    simp [stdVec, PiLp.single_apply, Pi.single_apply, Finset.sum_apply', PiLp.smul_apply, eq_comm]
  let L : ComplexVector n →L[ℂ] TangentVector M p :=
    mfderiv (ComplexModel n) (ComplexModel n)
      (extChartAt (ComplexModel n) p).symm (chartPt p p)
  have hv : L (tangentCoords p p v) = v :=
    chartVec_tangentCoords p p (mem_extChartAt_source p) v
  have hsum : L (∑ i : Fin n, tangentCoords p p v i • stdVec i) =
      ∑ i : Fin n, tangentCoords p p v i • L (stdVec i) := by
    simp only [map_sum, map_smul]
  rw [he, hv] at hsum
  rw [hsum]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- At each point a finite family of global holomorphic fields already spans
the actual tangent fibre. Uniform selection over all points is a later step. -/
theorem field_jets_spanning_at_point
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → Fin n → MvPolynomial (Fin n) ℂ),
      ∃ V : VectorField M, IsHolomorphicField V ∧
        ∀ p ∈ pts, JetAgreeField V p (Pj p) k)
    (p : M.Carrier) :
    ∃ V : Fin n → VectorField M,
      (∀ i, IsHolomorphicField (V i)) ∧
      Submodule.span ℂ (Set.range fun i => V i p) = ⊤ := by
  classical
  choose V hV heval using fun i : Fin n =>
    field_jets_evaluation_surjective hjets p (chartVec p p (stdVec i))
  refine ⟨V, hV, ?_⟩
  simpa only [heval] using chart_frame_span p

end Yau.NodeProofs.P03Aux
