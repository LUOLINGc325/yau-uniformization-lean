import Yau.Proofs.Y03PositiveSVD

/-! Positive singular frames of the given chart derivatives, with their exact determinant trace. -/

noncomputable section

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem derivativeMatrix_toEuclideanCLM (F : ComplexVector n → ComplexVector n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (derivativeMatrix F) = centerDeriv F := by
  apply ContinuousLinearMap.coe_injective
  change Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm (centerDeriv F).toLinearMap) = _
  exact Matrix.toEuclideanLin.apply_symm_apply _

theorem derivativeMatrix_det (F : ComplexVector n → ComplexVector n) :
    (derivativeMatrix F).det = LinearMap.det (centerDeriv F).toLinearMap := by
  rw [← LinearMap.det_toLin (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  change LinearMap.det (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm
    (centerDeriv F).toLinearMap)) = _
  rw [Matrix.toEuclideanLin.apply_symm_apply]

theorem matOpNorm_derivativeMatrix (F : ComplexVector n → ComplexVector n) :
    matOpNorm (derivativeMatrix F) = ‖centerDeriv F‖ := by
  unfold matOpNorm
  rw [derivativeMatrix_toEuclideanCLM]

open scoped Matrix.Norms.L2Operator in
theorem matOpNorm_unitary_mul {U : Herm n} (hU : Unitary U) (A : Herm n) :
    matOpNorm (U * A) = matOpNorm A := by
  change ‖U * A‖ = ‖A‖
  exact CStarRing.norm_mem_unitary_mul A hU

open scoped Matrix.Norms.L2Operator in
theorem matOpNorm_mul_unitary {V : Herm n} (hV : Unitary V) (A : Herm n) :
    matOpNorm (A * V) = matOpNorm A := by
  change ‖A * V‖ = ‖A‖
  exact CStarRing.norm_mul_mem_unitary A hV

open scoped Matrix.Norms.L2Operator in
theorem singular_diagonal_le_opNorm {A U V : Herm n} {σ : Fin n → ℝ}
    (hU : Unitary U) (hV : Unitary V) (hσ : ∀ i, 0 ≤ σ i)
    (hdiag : U.conjTranspose * A * V = Matrix.diagonal (fun i => (σ i : ℂ)))
    (i : Fin n) : σ i ≤ matOpNorm A := by
  calc
    σ i = ‖(σ i : ℂ)‖ := (Complex.norm_of_nonneg (hσ i)).symm
    _ ≤ ‖fun i => (σ i : ℂ)‖ := norm_le_pi_norm (fun i => (σ i : ℂ)) i
    _ = matOpNorm (Matrix.diagonal (fun i => (σ i : ℂ))) :=
      (Matrix.l2_opNorm_diagonal _).symm
    _ = matOpNorm A := by
      rw [← hdiag, matOpNorm_mul_unitary hV, matOpNorm_unitary_mul (unitary_conjTranspose hU)]

theorem positive_sorted_contraction_svd (A : Herm n) (hdet : A.det ≠ 0)
    (hA : matOpNorm A ≤ 1) :
    ∃ (U V : Herm n) (σ : Fin n → ℝ), Unitary U ∧ Unitary V ∧
      (∀ i, 0 < σ i ∧ σ i ≤ 1) ∧ Antitone σ ∧
      U.conjTranspose * A * V = Matrix.diagonal (fun i => (σ i : ℂ)) := by
  obtain ⟨U, V, σ, hU, hV, hσ, hanti, hdiag⟩ := positive_sorted_svd A hdet
  exact ⟨U, V, σ, hU, hV, fun i => ⟨hσ i,
    (singular_diagonal_le_opNorm hU hV (fun i => (hσ i).le) hdiag i).trans hA⟩,
    hanti, hdiag⟩

theorem singularFrames_of_shrinkingCharts {X : KahlerManifold n}
    {o : Pt X} {h : Flow X} {ρ : STF X} {r₀ r₁ σ C Cb t₀ : ℝ}
    {Φ : ℝ → ComplexVector n → Pt X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n}
    {f : ℝ → Pt X → ComplexVector n}
    (hCharts : ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f)
    (tk : ℕ → ℝ) (hpos : ∀ k, 0 < tk k) (hinc : ∀ k, tk k < tk (k + 1))
    (hlate : ∀ k, t₀ ≤ tk k) :
    ∃ E : Frames n, SingularFrames F tk E ∧
      ∀ k, ∑ i, rate F tk E k i =
        (ρ o (tk (k + 1)) - ρ o (tk k)) / Real.log (tk (k + 1) / tk k) := by
  have hdet : ∀ k, ‖(derivativeMatrix (F (tk k) (tk (k + 1)))).det‖ =
      Real.exp (-(ρ o (tk (k + 1)) - ρ o (tk k)) / 2) := by
    intro k
    rw [derivativeMatrix_det]
    exact (hCharts.2.2.2.2.2.1 (tk k) (tk (k + 1)) (hlate k) (hinc k).le).2.2.2.2.2.1
  have hstep : ∀ k, ∃ (U V : Herm n) (σ : Fin n → ℝ), Unitary U ∧ Unitary V ∧
      (∀ i, 0 < σ i ∧ σ i ≤ 1) ∧ Antitone σ ∧
      U.conjTranspose * derivativeMatrix (F (tk k) (tk (k + 1))) * V =
        Matrix.diagonal (fun i => (σ i : ℂ)) := by
    intro k
    apply positive_sorted_contraction_svd
    · intro hz
      have hnorm := hdet k
      rw [hz, norm_zero] at hnorm
      exact (ne_of_gt (Real.exp_pos _)) hnorm.symm
    · rw [matOpNorm_derivativeMatrix]
      exact (hCharts.2.2.2.2.2.1 (tk k) (tk (k + 1)) (hlate k) (hinc k).le).2.2.2.2.1
  choose U V σ hU hV hσ hanti hdiag using hstep
  let E : Frames n := ⟨V, U⟩
  have hlength : ∀ k i, singularLength F tk E k i = σ k i := by
    intro k i
    unfold singularLength transformedDerivative
    change ‖((U k).conjTranspose * derivativeMatrix (F (tk k) (tk (k + 1))) * V k) i i‖ = _
    rw [hdiag k, Matrix.diagonal_apply_eq, Complex.norm_of_nonneg ((hσ k i).1.le)]
  have hsing : SingularFrames F tk E := by
    intro k
    refine ⟨hpos k, hinc k, hV k, hU k, ?_, ?_, ?_⟩
    · change (U k).conjTranspose * derivativeMatrix (F (tk k) (tk (k + 1))) * V k = _
      rw [hdiag k]
      unfold diagonal
      simp only [hlength]
    · intro i
      simpa only [hlength] using hσ k i
    · intro i l hil
      rw [hlength, hlength]
      exact hanti k hil
  exact ⟨E, hsing, trace_rate_of_det (s := fun k => ρ o (tk k)) hsing hdet⟩

end Yau.Blueprint.Alignment.Y03Proof
