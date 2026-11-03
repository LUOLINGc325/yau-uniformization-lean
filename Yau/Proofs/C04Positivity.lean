import Yau.Proofs.F02Elementary
import Yau.Blueprint.Nodes

/-! Strict scalar positivity uses the genuine positive dimension of a noncompact manifold. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder MatrixOrder

namespace Yau.Proofs.C04Aux
open Yau Blueprint

/-- A connected noncompact complex manifold cannot have dimension zero. -/
theorem dimension_pos {n : ℕ} (M : ComplexManifold n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  letI : DiscreteTopology (ComplexVector 0) := inferInstance
  letI : DiscreteTopology M.Carrier := ChartedSpace.discreteTopology (ComplexVector 0) M.Carrier
  letI : Subsingleton M.Carrier := PreconnectedSpace.trivial_of_discrete
  letI : Finite M.Carrier := Finite.of_subsingleton
  letI : CompactSpace M.Carrier := Finite.compactSpace
  exact noncompact_univ M.Carrier isCompact_univ

/-- The trace pairing of two strictly positive Hermitian matrices is positive. -/
theorem trace_mul_re_pos {n : ℕ} (hn : 0 < n) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef) : 0 < (Matrix.trace (A * B)).re := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let S := CFC.sqrt A
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSinj : Function.Injective S.mulVec := by
    intro u v huv
    apply hA.mulVec_injective
    rw [← hSS, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, huv]
  have hp : (S * B * S).PosDef := by
    simpa only [hS.eq] using hB.conjTranspose_mul_mul_same hSinj
  have heq : Matrix.trace (S * B * S) = Matrix.trace (A * B) := by
    rw [Matrix.trace_mul_cycle, hSS]
  exact (Complex.pos_iff.mp (heq ▸ hp.trace_pos)).1

/-- In the original Harnack-complete flow, scalar curvature is strictly positive. -/
theorem scalar_pos {n : ℕ} (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (hH : HarnackCompleteness X o h) {t : ℝ} (ht : 0 ≤ t)
    (x : Pt X) : 0 < scalarCurvature (h t) x := by
  have hg : (gMat (h t) x).PosDef :=
    LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)
  exact trace_mul_re_pos (dimension_pos X.manifold) _ _ hg.inv (hH.2.2.1 t ht x)

end Yau.Proofs.C04Aux
