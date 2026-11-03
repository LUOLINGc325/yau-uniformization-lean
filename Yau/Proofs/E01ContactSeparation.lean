import Yau.Proofs.E01ConeClosed
import Yau.Proofs.E01FunctionalMatrix
import Yau.Proofs.E01FeasibleCompact

/-! Separation from the actual finite contact cone produces a strict matrix variation. -/

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

def realMatrixTrace : Herm n →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap

theorem realMatrixTrace_apply (A : Herm n) : realMatrixTrace A = (Matrix.trace A).re := rfl

theorem exists_strict_contact_separator
    (hn : 0 < n) (S : Set (ComplexVector n)) (hS : IsCompact S)
    (hunit : ∀ η ∈ S, ‖η‖ = 1)
    (hnot : (1 : Herm n) ∉ PointedCone.hull ℝ (contactRankOne '' S)) :
    ∃ H : Herm n, H.IsHermitian ∧ 0 < (Matrix.trace H).re ∧
      ∀ η ∈ S, ellipsoidQuadratic H η < 0 := by
  classical
  let G := contactRankOne '' S
  have hG : IsCompact G := hS.image (by
    unfold contactRankOne Matrix.vecMulVec
    fun_prop)
  have hτ : ∀ A ∈ G, realMatrixTrace A = 1 := by
    rintro A ⟨η, hη, rfl⟩
    rw [realMatrixTrace_apply, contactRankOne_trace, hunit η hη]
    norm_num
  have hclosed : IsClosed (PointedCone.hull ℝ G : Set (Herm n)) :=
    isClosed_cone_hull_of_compact_normalized_base (E := Herm n) (S := G)
      hG (realMatrixTrace (n := n)) hτ
  let C : ProperCone ℝ (Herm n) := ⟨PointedCone.hull ℝ G, hclosed⟩
  have hnotC : (1 : Herm n) ∉ C := hnot
  obtain ⟨L, hL, hLI⟩ := C.hyperplane_separation_point hnotC
  let H : Herm n := hermitianFunctionalMatrix (-L.toLinearMap)
  have hH : H.IsHermitian := hermitianFunctionalMatrix_isHermitian _
  have ht : (Matrix.trace H).re = -L 1 := by
    simpa [H] using
      trace_hermitianFunctionalMatrix (-L.toLinearMap) (1 : Herm n)
        (by simp [Matrix.IsHermitian])
  have htpos : 0 < (Matrix.trace H).re := by
    rw [ht]
    exact neg_pos.mpr hLI
  have hq : ∀ η ∈ S, ellipsoidQuadratic H η ≤ 0 := by
    intro η hη
    rw [quadratic_hermitianFunctionalMatrix]
    change -L (contactRankOne η) ≤ 0
    apply neg_nonpos.mpr
    exact hL _ (PointedCone.subset_hull ⟨η, hη, rfl⟩)
  let δ : ℝ := (Matrix.trace H).re / (2 * n)
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hδ : 0 < δ := div_pos htpos (mul_pos (by norm_num) hnR)
  have hδn : δ * (n : ℝ) = (Matrix.trace H).re / 2 := by
    dsimp only [δ]
    field_simp [hnR.ne']
  let H' : Herm n := H - (δ : ℂ) • 1
  have hδI : ((δ : ℂ) • (1 : Herm n)).IsHermitian := by
    unfold Matrix.IsHermitian
    simp
  have hH' : H'.IsHermitian := hH.sub hδI
  have ht' : (Matrix.trace H').re = (Matrix.trace H).re - δ * (n : ℝ) := by
    simp [H', Matrix.trace_sub, Matrix.trace_smul, Complex.mul_re]
  refine ⟨H', hH', ?_, ?_⟩
  · rw [ht', hδn]
    linarith
  · intro η hη
    change ellipsoidQuadratic (H - (δ : ℂ) • 1) η < 0
    rw [ellipsoidQuadratic_sub, ellipsoidQuadratic_real_smul,
      ellipsoidQuadratic_one, hunit η hη]
    norm_num
    exact (hq η hη).trans_lt hδ

end Yau.NodeProofs.E01Aux
