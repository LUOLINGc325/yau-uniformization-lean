import Yau.Proofs.C04MatrixSpectrum
import Yau.Proofs.C04RayleighScaling

/-! The concrete Rayleigh infimum and supremum are attained at Hermitian eigenvectors. -/

noncomputable section
open scoped ComplexOrder Matrix

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem spectral_upper_bound {A : Herm n} (hA : A.IsHermitian) (c : ℝ)
    (hc : ∀ i, hA.eigenvalues i ≤ c) : ((c : ℂ) • 1 - A).PosSemidef := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hAD : (U : Herm n) * D * (U : Herm n).conjTranspose = A := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def, U, D] using hA.spectral_theorem.symm
  have hD : ((c : ℂ) • (1 : Herm n) - D).PosSemidef := by
    have heq : (c : ℂ) • (1 : Herm n) - D = Matrix.diagonal (fun i => ((c - hA.eigenvalues i : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j <;> simp [D, Matrix.diagonal, hij]
    rw [heq]
    exact Matrix.PosSemidef.diagonal (fun i =>
      Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (hc i), by simp⟩)
  have hh := hD.conjTranspose_mul_mul_same (U : Herm n).conjTranspose
  simp only [Matrix.conjTranspose_conjTranspose] at hh
  have hu : (U : Herm n) * (U : Herm n).conjTranspose = 1 := Unitary.coe_mul_star_self U
  have heq : (U : Herm n) * ((c : ℂ) • 1 - D) * (U : Herm n).conjTranspose = (c : ℂ) • 1 - A := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hAD, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hu]
  rwa [heq] at hh

theorem matrixQuadratic_one (v : ComplexVector n) : matrixQuadratic (1 : Herm n) v = ‖v‖ ^ 2 := by
  unfold matrixQuadratic
  rw [Matrix.one_mulVec, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm

theorem matrixQuadratic_sub (A B : Herm n) (v : ComplexVector n) :
    matrixQuadratic (A - B) v = matrixQuadratic A v - matrixQuadratic B v := by
  simp only [matrixQuadratic, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem rayleigh_lower_of_spectral {A : Herm n} (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ i, c ≤ hA.eigenvalues i) (v : ComplexVector n) (hv : v ≠ 0) :
    c ≤ matrixQuadratic A v / matrixQuadratic 1 v := by
  have hd : 0 < matrixQuadratic (1 : Herm n) v := matrixQuadratic_pos _ Matrix.PosDef.one v hv
  have hh := (spectral_lower_bound hA c hc).re_dotProduct_nonneg (WithLp.ofLp v)
  change 0 ≤ matrixQuadratic (A - (c : ℂ) • 1) v at hh
  rw [matrixQuadratic_sub, matrixQuadratic_real_smul] at hh
  exact (le_div_iff₀ hd).mpr (by linarith)

theorem rayleigh_upper_of_spectral {A : Herm n} (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ i, hA.eigenvalues i ≤ c) (v : ComplexVector n) (hv : v ≠ 0) :
    matrixQuadratic A v / matrixQuadratic 1 v ≤ c := by
  have hd : 0 < matrixQuadratic (1 : Herm n) v := matrixQuadratic_pos _ Matrix.PosDef.one v hv
  have hh := (spectral_upper_bound hA c hc).re_dotProduct_nonneg (WithLp.ofLp v)
  change 0 ≤ matrixQuadratic ((c : ℂ) • 1 - A) v at hh
  rw [matrixQuadratic_sub, matrixQuadratic_real_smul] at hh
  exact (div_le_iff₀ hd).mpr (by linarith)

theorem eigenvector_rayleigh {A : Herm n} (hA : A.IsHermitian) (i : Fin n) :
    matrixQuadratic A (hA.eigenvectorBasis i) / matrixQuadratic 1 (hA.eigenvectorBasis i) = hA.eigenvalues i := by
  have hnum : matrixQuadratic A (hA.eigenvectorBasis i) = hA.eigenvalues i := (hA.eigenvalues_eq i).symm
  rw [hnum, matrixQuadratic_one, hA.eigenvectorBasis.orthonormal.1 i]
  simp

theorem relMin_eq_of_minimal_eigenvalue {A : Herm n} (hA : A.IsHermitian)
    (i : Fin n) (hi : ∀ j, hA.eigenvalues i ≤ hA.eigenvalues j) :
    relMinEigenvalue 1 A = hA.eigenvalues i := by
  have hne : hA.eigenvectorBasis i ≠ 0 := by
    intro hz
    have hh := hA.eigenvectorBasis.orthonormal.1 i
    simp only [hz, norm_zero, zero_ne_one] at hh
  letI : Nonempty {v : ComplexVector n // v ≠ 0} := ⟨⟨_, hne⟩⟩
  have hlo : hA.eigenvalues i ≤ relMinEigenvalue 1 A :=
    le_ciInf (fun v => rayleigh_lower_of_spectral hA hi v.1 v.2)
  have hb : BddBelow (Set.range (fun v : {v : ComplexVector n // v ≠ 0} =>
      matrixQuadratic A v.1 / matrixQuadratic 1 v.1)) :=
    ⟨hA.eigenvalues i, by rintro _ ⟨v, rfl⟩; exact rayleigh_lower_of_spectral hA hi v.1 v.2⟩
  have hhi := ciInf_le hb (⟨hA.eigenvectorBasis i, hne⟩ : {v : ComplexVector n // v ≠ 0})
  exact le_antisymm (hhi.trans_eq (eigenvector_rayleigh hA i)) hlo

theorem relMax_eq_of_maximal_eigenvalue {A : Herm n} (hA : A.IsHermitian)
    (i : Fin n) (hi : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues i) :
    relMaxEigenvalue 1 A = hA.eigenvalues i := by
  have hne : hA.eigenvectorBasis i ≠ 0 := by
    intro hz
    have hh := hA.eigenvectorBasis.orthonormal.1 i
    simp only [hz, norm_zero, zero_ne_one] at hh
  letI : Nonempty {v : ComplexVector n // v ≠ 0} := ⟨⟨_, hne⟩⟩
  have hhi : relMaxEigenvalue 1 A ≤ hA.eigenvalues i :=
    ciSup_le (fun v => rayleigh_upper_of_spectral hA hi v.1 v.2)
  have hb : BddAbove (Set.range (fun v : {v : ComplexVector n // v ≠ 0} =>
      matrixQuadratic A v.1 / matrixQuadratic 1 v.1)) :=
    ⟨hA.eigenvalues i, by rintro _ ⟨v, rfl⟩; exact rayleigh_upper_of_spectral hA hi v.1 v.2⟩
  have hlo := le_ciSup hb (⟨hA.eigenvectorBasis i, hne⟩ : {v : ComplexVector n // v ≠ 0})
  exact le_antisymm hhi ((eigenvector_rayleigh hA i).symm.trans_le hlo)

end Yau.Proofs.C04Aux
