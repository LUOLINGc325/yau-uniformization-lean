import Yau.Proofs.P04TrivialLine

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder InnerProductSpace
open Bundle Module

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- Scalar top alternating forms are continuous by their actual determinant
coordinate formula in a finite basis. -/
theorem continuous_top_alternating {V ι : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℂ V) (A : V [⋀^ι]→ₗ[ℂ] ℂ) : Continuous A := by
  have hdet : Continuous (fun v : ι → V => b.det v) := by
    simp only [Basis.det_apply]
    apply Continuous.matrix_det
    exact continuous_pi (fun i => continuous_pi (fun j =>
      (b.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)))
  have heq : (A : (ι → V) → ℂ) = fun v => A b * b.det v := by
    funext v
    exact congrArg (fun L : V [⋀^ι]→ₗ[ℂ] ℂ => L v) (A.eq_smul_basis_det b)
  rw [heq]
  exact continuous_const.mul hdet

def scalarToCoefficient : ℂ →L[ℂ] ComplexVector 1 :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (stdVec 0)

theorem scalarToCoefficient_apply (c : ℂ) (i : Fin 1) : scalarToCoefficient c i=c := by
  fin_cases i
  simp [scalarToCoefficient,stdVec]

def coefficientToScalar : ComplexVector 1 →L[ℂ] ℂ :=
  EuclideanSpace.proj 0

/-- Actual canonical tensors become top forms with values in the flat line. -/
def canonicalToTop (S : CanonicalSection M) : BundleDbar.NQForm (CanonicalCoefficients M) 0 :=
  fun x => ⟨AlternatingMap.constOfIsEmpty ℝ (TangentVector M x) (Fin 0)
    (scalarToCoefficient.toLinearMap.compAlternatingMap (S x).toAlternatingMap), by
      intro v i
      exact Fin.elim0 i⟩

def topToCanonical (u : BundleDbar.NQForm (CanonicalCoefficients M) 0) : CanonicalSection M :=
  fun x =>
    { coefficientToScalar.toLinearMap.compAlternatingMap ((u x).1 Fin.elim0) with
      cont := continuous_top_alternating (EuclideanSpace.basisFun (Fin n) ℂ).toBasis _ }

theorem topToCanonical_apply (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (x : M.Carrier) (v : Fin n → TangentVector M x) :
    topToCanonical u x v = ((u x).1 Fin.elim0 v) 0 := rfl

theorem topToCanonical_canonicalToTop (S : CanonicalSection M) :
    topToCanonical (canonicalToTop S) = S := by
  funext x
  ext v
  exact scalarToCoefficient_apply _ 0

theorem canonicalToTop_topToCanonical (u : BundleDbar.NQForm (CanonicalCoefficients M) 0) :
    canonicalToTop (topToCanonical u) = u := by
  funext x
  apply Subtype.ext
  apply AlternatingMap.ext
  intro w
  have hw : w=Fin.elim0 := Subsingleton.elim _ _
  rw [hw]
  apply AlternatingMap.ext
  intro v
  ext i
  have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact scalarToCoefficient_apply _ 0

theorem coefficient_canonicalToTop (S : CanonicalSection M) (a : M.Carrier)
    (z : ComplexVector n) :
    BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) (canonicalToTop S) a z Fin.elim0 0 =
      canonicalCoeff S a z := by
  simp only [BundleDbar.coefficients,coefficient_localTriv,
    Bundle.Trivial.continuousLinearMapAt_trivialization,ContinuousLinearMap.id_apply]
  exact scalarToCoefficient_apply _ 0

theorem coefficient_topToCanonical (u : BundleDbar.NQForm (CanonicalCoefficients M) 0)
    (a : M.Carrier) (z : ComplexVector n) :
    canonicalCoeff (topToCanonical u) a z =
      BundleDbar.coefficients (r := 1) (CanonicalCoefficients M) u a z Fin.elim0 0 := by
  rw [← coefficient_canonicalToTop,canonicalToTop_topToCanonical]

end Yau.Proofs.P04Aux
