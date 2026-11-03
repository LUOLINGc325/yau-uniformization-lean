import Yau.Blueprint.Nodes
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-! Exact bridges between the frozen matrix quotient and Mathlib's Rayleigh quotient. -/
noncomputable section
open scoped Matrix ComplexOrder Topology
open Set
namespace Yau.Proofs.C03Aux.Rayleigh
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def quadratic (H : Herm n) (v : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re

def operator (H : Herm n) : ComplexVector n →L[ℂ] ComplexVector n :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) H

theorem operator_apply (H : Herm n) (v : ComplexVector n) :
    operator H v = WithLp.toLp 2 (H *ᵥ WithLp.ofLp v) := rfl

theorem quadratic_eq_inner (H : Herm n) (v : ComplexVector n) :
    quadratic H v = (inner ℂ v (operator H v)).re := by
  simp [quadratic, operator_apply, PiLp.inner_apply, dotProduct, mul_comm]

theorem quadratic_one (v : ComplexVector n) : quadratic (1 : Herm n) v = ‖v‖ ^ 2 := by
  rw [quadratic_eq_inner]
  rw [operator_apply, Matrix.one_mulVec, WithLp.toLp_ofLp]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) v

theorem quadratic_pos (H : Herm n) (hH : H.PosDef) (v : ComplexVector n) (hv : v ≠ 0) :
    0 < quadratic H v := by
  have hv' : WithLp.ofLp v ≠ 0 := by
    intro h
    apply hv
    apply WithLp.ofLp_injective 2
    simpa using h
  exact (Complex.pos_iff.mp (hH.dotProduct_mulVec_pos hv')).1

theorem operator_selfAdjoint (H : Herm n) (hH : H.IsHermitian) :
    IsSelfAdjoint (operator H) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hH

theorem operator_reApplyInnerSelf (H : Herm n) (v : ComplexVector n) :
    (operator H).reApplyInnerSelf v = quadratic H v := by
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, quadratic_eq_inner]
  exact inner_re_symm _ _

theorem operator_rayleigh (H : Herm n) (v : ComplexVector n) :
    (operator H).rayleighQuotient v = quadratic H v / quadratic (1 : Herm n) v := by
  rw [ContinuousLinearMap.rayleighQuotient, operator_reApplyInnerSelf, quadratic_one]

theorem relMin_eq_iInf (H : Herm n) :
    relMinEigenvalue (1 : Herm n) H =
      ⨅ v : {v : ComplexVector n // v ≠ 0}, (operator H).rayleighQuotient v := by
  simp only [relMinEigenvalue, operator_rayleigh, quadratic]

theorem relMax_eq_iSup (H : Herm n) :
    relMaxEigenvalue (1 : Herm n) H =
      ⨆ v : {v : ComplexVector n // v ≠ 0}, (operator H).rayleighQuotient v := by
  simp only [relMaxEigenvalue, operator_rayleigh, quadratic]

theorem rayleigh_bddBelow (H : Herm n) :
    BddBelow (Set.range fun v : {v : ComplexVector n // v ≠ 0} =>
      (operator H).rayleighQuotient v) := by
  refine ⟨-‖operator H‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact (abs_le.mp ((operator H).rayleighQuotient_le_norm v)).1

theorem rayleigh_bddAbove (H : Herm n) :
    BddAbove (Set.range fun v : {v : ComplexVector n // v ≠ 0} =>
      (operator H).rayleighQuotient v) := by
  refine ⟨‖operator H‖, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact (abs_le.mp ((operator H).rayleighQuotient_le_norm v)).2

theorem rayleigh_bounds (H : Herm n) (v : ComplexVector n) (hv : v ≠ 0) :
    relMinEigenvalue (1 : Herm n) H ≤ quadratic H v / ‖v‖ ^ 2 ∧
      quadratic H v / ‖v‖ ^ 2 ≤ relMaxEigenvalue (1 : Herm n) H := by
  rw [relMin_eq_iInf, relMax_eq_iSup]
  have he : quadratic H v / ‖v‖ ^ 2 = (operator H).rayleighQuotient v := by
    rw [operator_rayleigh, quadratic_one]
  rw [he]
  exact ⟨ciInf_le (rayleigh_bddBelow H) ⟨v, hv⟩, le_ciSup (rayleigh_bddAbove H) ⟨v, hv⟩⟩

end Yau.Proofs.C03Aux.Rayleigh
