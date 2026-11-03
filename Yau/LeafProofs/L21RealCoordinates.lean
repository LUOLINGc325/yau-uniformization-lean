import Yau.LeafProofs.L21CompactWeakJets
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The actual volume-preserving real coordinates used to transport the
compact weak jets to finite-product Lebesgue space. -/

open MeasureTheory
open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def realDimension (n : ℕ) := Fintype.card (Yau.RIdx n)

def realIndex (n : ℕ) : Yau.RIdx n ≃ Fin (realDimension n) := Fintype.equivFin _

def realBasis (n : ℕ) : OrthonormalBasis (Yau.RIdx n) ℝ (X n) :=
  (Pi.orthonormalBasis fun _ : Fin n => Complex.orthonormalBasisOneI).reindex
    (Equiv.sigmaEquivProd (Fin n) (Fin 2))

theorem realBasis_apply (n : ℕ) (a : Yau.RIdx n) : realBasis n a = Yau.realVec a := by
  rcases a with ⟨i, j⟩
  fin_cases j <;> ext k <;>
    simp [realBasis, OrthonormalBasis.reindex_apply, Pi.orthonormalBasis_apply,
      Complex.coe_orthonormalBasisOneI, Yau.realVec, EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]

def realCoordinateBasis (n : ℕ) : OrthonormalBasis (Fin (realDimension n)) ℝ (X n) :=
  (realBasis n).reindex (realIndex n)

def realCoordinates (n : ℕ) : X n ≃L[ℝ] (Fin (realDimension n) → ℝ) :=
  (realCoordinateBasis n).repr.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (realDimension n) => ℝ))

theorem realCoordinateBasis_index (a : Yau.RIdx n) :
    realCoordinateBasis n (realIndex n a) = Yau.realVec a := by
  simp only [realCoordinateBasis, OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, realBasis_apply]

theorem realCoordinates_realVec (a : Yau.RIdx n) :
    realCoordinates n (Yau.realVec a) = Pi.single (realIndex n a) 1 := by
  rw [← realCoordinateBasis_index a]
  ext j
  simp [realCoordinates, OrthonormalBasis.repr_self, PiLp.single_apply, Pi.single_apply]

theorem realCoordinates_symm_single (j : Fin (realDimension n)) :
    (realCoordinates n).symm (Pi.single j 1) = Yau.realVec ((realIndex n).symm j) := by
  apply (realCoordinates n).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, realCoordinates_realVec, Equiv.apply_symm_apply]

theorem realCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (realCoordinates n) (Yau.lebesgueC n) volume := by
  rw [Yau.LeafProofs.lebesgueC_eq_volume]
  change MeasurePreserving (fun x => WithLp.ofLp ((realCoordinateBasis n).repr x)) volume volume
  exact (PiLp.volume_preserving_ofLp _).comp (realCoordinateBasis n).measurePreserving_repr

theorem realCoordinates_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (realCoordinates n).symm volume (Yau.lebesgueC n) := by
  have he : MeasurePreserving (realCoordinates n).toHomeomorph.toMeasurableEquiv
      (Yau.lebesgueC n) volume := realCoordinates_measurePreserving n
  exact he.symm

theorem realCoordinates_directional {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : (Fin (realDimension n) → ℝ) → F} (hφ : Differentiable ℝ φ)
    (x : X n) (a : Yau.RIdx n) :
    fderiv ℝ (φ ∘ realCoordinates n) x (Yau.realVec a) =
      fderiv ℝ φ (realCoordinates n x) (Pi.single (realIndex n a) 1) := by
  rw [fderiv_comp x (hφ _) (realCoordinates n).differentiableAt, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.fderiv]
  change fderiv ℝ φ (realCoordinates n x) (realCoordinates n (Yau.realVec a)) = _
  rw [realCoordinates_realVec]

theorem realCoordinates_symm_directional {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : X n → F} (hφ : Differentiable ℝ φ)
    (x : Fin (realDimension n) → ℝ) (j : Fin (realDimension n)) :
    fderiv ℝ (φ ∘ (realCoordinates n).symm) x (Pi.single j 1) =
      fderiv ℝ φ ((realCoordinates n).symm x) (Yau.realVec ((realIndex n).symm j)) := by
  rw [fderiv_comp x (hφ _) (realCoordinates n).symm.differentiableAt, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.fderiv]
  change fderiv ℝ φ ((realCoordinates n).symm x) ((realCoordinates n).symm (Pi.single j 1)) = _
  rw [realCoordinates_symm_single]

end Yau.LeafProofs.L21Aux
