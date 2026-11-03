import Yau.Proofs.B01Coordinate
import Yau.LeafProofs.L14Calculus

open scoped Manifold Topology ContDiff
open Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def sectionTopForm (c : DiscCoordinate M) (s : Section E) : BundleDbar.NQForm E 0 :=
  fun x => ⟨AlternatingMap.constOfIsEmpty ℝ (TangentVector M x) (Fin 0)
    (AlternatingMap.ofSubsingleton ℂ (TangentVector M x) (E x) (0 : Fin 1)
      ((discDerivative c x).smulRight (s x))), by
        intro v i
        exact Fin.elim0 i⟩

theorem sectionTopForm_spec (c : DiscCoordinate M) (s : Section E) :
    IsSectionTopForm E c s (sectionTopForm E c s) := by
  intro x v w
  rfl

theorem sectionTopFormRealization : SectionTopFormRealization (r := r) E := by
  intro c hc s
  refine ⟨sectionTopForm E c s, sectionTopForm_spec E c s, ?_⟩
  intro a z hz
  unfold BundleDbar.coefficients
  rw [sectionTopForm_spec E c s]
  rw [map_smul]
  change _ • sectionCoefficients (r := r) E s a z = _
  rw [LeafProofs.L14Aux.wirt_eq_fderiv_of_complex_differentiable
    (fun w => c (chartInv a w)) z (stdVec 0)
      ((disc_inChart_contDiffAt c hc a hz.1).differentiableAt (by simp)),
    disc_inChart_fderiv c hc a hz.1]

theorem topFormSectionRecovery : TopFormSectionRecovery E := by
  intro c hc u
  let s : Section E := fun x =>
    ((u x).1 Fin.elim0) (fun _ : Fin 1 => discCoordinateVector c x)
  refine ⟨s, ?_, ?_⟩
  · intro x v w
    have hv : v = Fin.elim0 := Subsingleton.elim _ _
    rw [hv]
    let b : ℂ := mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x (w 0)
    have hw : w = fun _ : Fin 1 => b • discCoordinateVector c x := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact tangent_eq_discCoordinateVector c hc x (w 0)
    change (((u x).1 Fin.elim0) w) = b • s x
    rw [hw]
    simpa only [Fin.prod_univ_one] using
      (((u x).1 Fin.elim0).map_smul_univ (fun _ : Fin 1 => b)
        (fun _ : Fin 1 => discCoordinateVector c x))
  · intro t ht
    funext x
    have h := ht x Fin.elim0 (fun _ : Fin 1 => discCoordinateVector c x)
    exact (by simpa only [discCoordinateVector_map c hc, one_smul] using h.symm)

end Yau.Proofs.B01Aux
