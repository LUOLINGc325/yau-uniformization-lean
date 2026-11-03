import Yau.Proofs.C04Positivity
import Yau.Proofs.C04Scaling

/-! The normalized Ricci lower bound is the genuine Rayleigh infimum. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def matrixQuadratic (H : Herm n) (v : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re

theorem matrixQuadratic_real_smul (c : ℝ) (H : Herm n) (v : ComplexVector n) :
    matrixQuadratic ((c : ℂ) • H) v = c * matrixQuadratic H v := by
  simp only [matrixQuadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem matrixQuadratic_pos (H : Herm n) (hH : H.PosDef)
    (v : ComplexVector n) (hv : v ≠ 0) : 0 < matrixQuadratic H v := by
  have hv' : WithLp.ofLp v ≠ 0 := by
    intro hh
    apply hv
    apply WithLp.ofLp_injective
    simpa only [WithLp.ofLp_zero] using hh
  exact (Complex.pos_iff.mp (hH.dotProduct_mulVec_pos hv')).1

theorem nonzero_complexVector_nonempty (hn : 0 < n) :
    Nonempty {v : ComplexVector n // v ≠ 0} := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨⟨stdVec i, ?_⟩⟩
  intro h
  have hh := congrArg (fun v : ComplexVector n => v i) h
  simpa [stdVec, EuclideanSpace.single] using hh

/-- A positive Rayleigh infimum is below every actual nonzero quotient. -/
theorem relMin_le_of_positive {H A : Herm n} (hpos : 0 < relMinEigenvalue H A)
    (v : ComplexVector n) (hv : v ≠ 0) :
    relMinEigenvalue H A ≤ matrixQuadratic A v / matrixQuadratic H v := by
  let q : {v : ComplexVector n // v ≠ 0} → ℝ :=
    fun v => matrixQuadratic A v.1 / matrixQuadratic H v.1
  have hbd : BddBelow (Set.range q) := by
    by_contra hn
    have hz := ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow (Set.range q) hn
    change 0 < sInf (Set.range q) at hpos
    rw [hz] at hpos
    norm_num at hpos
  exact ciInf_le hbd ⟨v, hv⟩

/-- The physical-time Ricci lower bound divided by q is exactly the lower
bound for the same scalar-normalized metric. No eigenvector choice is made. -/
theorem normalized_ricci_lower (X : KahlerManifold n) (o : Pt X) (h : Flow X)
    (t b : ℝ) (ht : 0 < t) (hb : 0 < b) (hR : 0 < scalarCurvature (h t) o)
    (hmin : b * clockSpeed o h t ≤ ricciMin o h t) :
    b ≤ relMinEigenvalue
      (gMat (scaleField (scalarCurvature (h t) o) hR (h t)) o)
      (ricci (scaleField (scalarCurvature (h t) o) hR (h t)) o) := by
  letI := nonzero_complexVector_nonempty (dimension_pos X.manifold)
  have hq : 0 < clockSpeed o h t := mul_pos ht hR
  have hminpos : 0 < ricciMin o h t := (mul_pos hb hq).trans_le hmin
  rw [gMat_scaleField, ricci_scaleField]
  apply le_ciInf
  intro v
  have hg : (gMat (h t) o).PosDef :=
    LeafProofs.L18Aux.hMat_posDef (h t) o (chartPt o o) (mem_extChartAt_target o)
  have hD := matrixQuadratic_pos _ hg v.1 v.2
  have hray := relMin_le_of_positive hminpos v.1 v.2
  change ricciMin o h t ≤
    matrixQuadratic ((t : ℂ) • ricci (h t) o) v.1 /
      matrixQuadratic (gMat (h t) o) v.1 at hray
  rw [matrixQuadratic_real_smul] at hray
  have hstep := (le_div_iff₀ hD).mp (hmin.trans hray)
  have hbound : b * (scalarCurvature (h t) o * matrixQuadratic (gMat (h t) o) v.1) ≤
      matrixQuadratic (ricci (h t) o) v.1 := by
    apply (mul_le_mul_iff_right₀ ht).mp
    dsimp only [clockSpeed] at hstep
    nlinarith
  change b ≤ matrixQuadratic (ricci (h t) o) v.1 /
    matrixQuadratic ((scalarCurvature (h t) o : ℂ) • gMat (h t) o) v.1
  rw [matrixQuadratic_real_smul]
  exact (le_div_iff₀ (mul_pos hR hD)).mpr hbound

end Yau.Proofs.C04Aux
