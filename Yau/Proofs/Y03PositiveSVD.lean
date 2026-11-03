import Yau.Proofs.Y03SVD

/-! Positive sorted singular decomposition, built from the Hermitian spectral theorem. -/

noncomputable section

open scoped ComplexOrder

namespace Yau.Blueprint.Alignment.Y03Proof

open Yau

variable {n : ℕ}

theorem unitary_of_conjTranspose_mul {A : Herm n} (hA : A.conjTranspose * A = 1) :
    Unitary A := by
  exact Matrix.mem_unitaryGroup_iff'.2 hA

theorem unitary_reindex_columns {A : Herm n} (hA : Unitary A) (e : Equiv.Perm (Fin n)) :
    Unitary (A.submatrix id e) := by
  apply unitary_of_conjTranspose_mul
  ext i j
  have hij := congrFun (congrFun hA.1 (e i)) (e j)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    id_eq, Matrix.one_apply, e.apply_eq_iff_eq] using hij

theorem conjugate_reindex_columns (A B : Herm n) (e : Equiv.Perm (Fin n)) :
    (A.submatrix id e).conjTranspose * B * (A.submatrix id e) =
      (A.conjTranspose * B * A).submatrix e e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq]

theorem positive_sorted_svd (A : Herm n) (hdet : A.det ≠ 0) :
    ∃ (U V : Herm n) (σ : Fin n → ℝ), Unitary U ∧ Unitary V ∧
      (∀ i, 0 < σ i) ∧ Antitone σ ∧
      U.conjTranspose * A * V = Matrix.diagonal (fun i => (σ i : ℂ)) := by
  have hinj : Function.Injective A.mulVec := by
    apply Matrix.mulVec_injective_iff_isUnit.2
    exact (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet)
  have hpos := Matrix.PosDef.conjTranspose_mul_self A hinj
  let H := hpos.isHermitian
  let eig := H.eigenvalues
  let e : Equiv.Perm (Fin n) := Tuple.sort (α := ℝᵒᵈ) eig
  let V₀ : Herm n := H.eigenvectorUnitary
  let V := V₀.submatrix id e
  let σ : Fin n → ℝ := fun i => Real.sqrt (eig (e i))
  let D : Herm n := Matrix.diagonal (fun i => (σ i : ℂ))
  let Dinv : Herm n := Matrix.diagonal (fun i => (σ i : ℂ)⁻¹)
  have hV₀ : Unitary V₀ := H.eigenvectorUnitary.property
  have hV : Unitary V := unitary_reindex_columns hV₀ e
  have heigPos : ∀ i, 0 < eig i := hpos.eigenvalues_pos
  have hσ : ∀ i, 0 < σ i := fun i => Real.sqrt_pos.2 (heigPos (e i))
  have hσne : ∀ i, (σ i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (ne_of_gt (hσ i))
  have hsort : Antitone σ := by
    intro i j hij
    apply Real.sqrt_le_sqrt
    exact Tuple.monotone_sort (α := ℝᵒᵈ) eig hij
  have hdiag₀ : V₀.conjTranspose * (A.conjTranspose * A) * V₀ =
      Matrix.diagonal (fun i => (eig i : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, V₀, eig, Function.comp_def] using
      H.conjStarAlgAut_star_eigenvectorUnitary
  have hdiag : V.conjTranspose * (A.conjTranspose * A) * V = D * D := by
    rw [conjugate_reindex_columns V₀ (A.conjTranspose * A) e, hdiag₀]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.submatrix_apply, Matrix.diagonal_apply_eq]
      change (eig (e i) : ℂ) = (σ i : ℂ) * (σ i : ℂ)
      rw [← Complex.ofReal_mul]
      congr 1
      exact (Real.mul_self_sqrt (heigPos (e i)).le).symm
    · simp [Matrix.submatrix_apply, hij, e.apply_eq_iff_eq]
  have hDleft : Dinv * D = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, hσne]
  have hDright : D * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal_apply, Matrix.one_apply, hσne]
  have hDstar : Dinv.conjTranspose = Dinv := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Dinv, Matrix.conjTranspose_apply]
    · simp [Dinv, Matrix.conjTranspose_apply, hij, Ne.symm hij]
  let U := A * V * Dinv
  have hU : Unitary U := by
    apply unitary_of_conjTranspose_mul
    change (A * V * Dinv).conjTranspose * (A * V * Dinv) = 1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDstar]
    calc
      Dinv * (V.conjTranspose * A.conjTranspose) * (A * V * Dinv) =
          Dinv * (V.conjTranspose * (A.conjTranspose * A) * V) * Dinv := by noncomm_ring
      _ = Dinv * (D * D) * Dinv := by rw [hdiag]
      _ = (Dinv * D) * (D * Dinv) := by noncomm_ring
      _ = 1 := by rw [hDleft, hDright, Matrix.one_mul]
  refine ⟨U, V, σ, hU, hV, hσ, hsort, ?_⟩
  change (A * V * Dinv).conjTranspose * A * V = D
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDstar]
  calc
    Dinv * (V.conjTranspose * A.conjTranspose) * A * V =
        Dinv * (V.conjTranspose * (A.conjTranspose * A) * V) := by noncomm_ring
    _ = Dinv * (D * D) := by rw [hdiag]
    _ = (Dinv * D) * D := by noncomm_ring
    _ = D := by rw [hDleft, Matrix.one_mul]

end Yau.Blueprint.Alignment.Y03Proof
