import Yau.Proofs.V04PositiveReplacementPolynomial
import Yau.Proofs.V04PositiveReplacementSpectral
import Yau.Proofs.V04CotangentSymplectic

/-! Uniform finite-dimensional error, before delta and every original disc
and its caller-supplied normalized frame. -/
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.PositiveReplacementAux
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem entry_le_of_frobSq {Q : ℝ} (hQ : 0 ≤ Q) (J : CotangentMatrix n)
    (hJ : matrixFrobSq J ≤ Q ^ 2) (i j : CotangentIndex n) : ‖J i j‖ ≤ Q := by
  have hrow : ‖J i j‖ ^ 2 ≤ ∑ k, ‖J i k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖J i k‖ ^ 2)
      (fun k _ => sq_nonneg ‖J i k‖) (Finset.mem_univ j)
  have hall : (∑ k, ‖J i k‖ ^ 2) ≤ matrixFrobSq J := by
    exact Finset.single_le_sum (f := fun k => ∑ l, ‖J k l‖ ^ 2)
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg ‖J k l‖))
      (Finset.mem_univ i)
  exact (sq_le_sq₀ (norm_nonneg _) hQ).mp (hrow.trans (hall.trans hJ))

theorem matrix_replacement_bound {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 ≤ Q) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ (A J : CotangentMatrix n), A.IsHermitian → rectOpNorm A ≤ M →
      matrixFrobSq J ≤ Q ^ 2 →
      |bivectorCost A J - bivectorCost (smoothMajorant δ A) J| ≤
        L * ((Matrix.trace (matrixNegative A)).re + δ) := by
  obtain ⟨L, hL, hpoly⟩ := bivectorCost_entry_lipschitz (n := n) (M := M + 2)
    (by positivity) hQ
  refine ⟨2 * L, by positivity, fun {δ} hδ hδ1 A J hA hbound hJ => ?_⟩
  have hneg := (Complex.nonneg_iff.mp (matrixNegative_posSemidef A).trace_nonneg).1
  have hh := hpoly A (smoothMajorant δ A) J
    (fun i j => ((V03Proof.matrix_entry_norm_le_rectOpNorm A i j).trans hbound).trans (by linarith))
    (fun i j => ((V03Proof.matrix_entry_norm_le_rectOpNorm _ i j).trans
      (smoothMajorant_rectOpNorm_bound hδ hM A hA hbound)).trans (by linarith))
    (entry_le_of_frobSq hQ J hJ) (by positivity : 0 ≤ (Matrix.trace (matrixNegative A)).re + 3 * δ / 2)
    (symbol_smoothing_entry_error hδ A hA)
  exact hh.trans (by nlinarith)

theorem fixed_index_matrix_replacement_bound {d : VariationData X q}
    (hd : VariationSetup d) {a : ℕ} (hsymbol : SymbolBounds d a) (j : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → ∀ θ : ℝ,
      |bivectorCost (boundarySymbol d j a F E (circlePoint θ)) (frameBivector (E (circlePoint θ))) -
        bivectorCost (smoothMajorant δ (boundarySymbol d j a F E (circlePoint θ)))
          (frameBivector (E (circlePoint θ)))| ≤
      L * ((Matrix.trace (matrixNegative (boundarySymbol d j a F E (circlePoint θ)))).re + δ) := by
  obtain ⟨M, hM, hsymbol⟩ := hsymbol j
  obtain ⟨Q, hQ, hframe⟩ := variation_frameBivector_uniform_bound hd j
  obtain ⟨L, hL, hbound⟩ := matrix_replacement_bound (n := n) hM hQ.le
  refine ⟨L, hL, fun {δ} hδ hδ1 F E hF hE θ => ?_⟩
  exact hbound hδ hδ1 _ _ ((hsymbol F E hF hE).1 θ).1
    ((hsymbol F E hF hE).1 θ).2 (hframe F E hF hE _ (V03Proof.circlePoint_mem_closedBall θ))

end Yau.Blueprint.V04Proof.PositiveReplacementAux
