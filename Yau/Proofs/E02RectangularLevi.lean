import Yau.Proofs.E02LogGramCalculus
import Yau.Proofs.E02LogGramLevi
import Yau.Proofs.E02ProjectorPenaltyLevi

open Matrix Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Actual logdet of MMᴴ, with every ordinary calculus hypothesis
supplied by the proved smooth inverse and determinant. -/
theorem logGram_rectLevi_eq {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    rectLevi logGram M Z = (Matrix.trace (projectorTangent M Z*(projectorTangent M Z)ᴴ)).re := by
  have hAt : ContDiffAt ℝ ∞ (logGram (n := n) (m := m)) M :=
    (logGram_contDiffOn n m).contDiffAt
      ((isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM))
  have hFirst : ∀ᶠ N in 𝓝 M, ∀ V : Rect n m,
      fderiv ℝ logGram N V = (Matrix.trace ((N*Nᴴ)⁻¹*(N*Vᴴ+V*Nᴴ))).re := by
    filter_upwards [(isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM)] with N hN
    exact fun V => logGram_fderiv_apply N V ((fullRankRect_iff_posDef N).mp hN)
  exact rectLevi_eq_tangent_of_gram_logderivative logGram M Z hM
    (hAt.of_le (by simp)) ((inverseGram_contDiffAt M hM).differentiableAt (by simp)) hFirst

theorem logGram_rectLevi_formula {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    rectLevi logGram M Z = (Matrix.trace ((M*Mᴴ)⁻¹*Z*(1-rowProjector M)*Zᴴ)).re := by
  rw [logGram_rectLevi_eq M Z hM,trace_projectorTangent_mul_adjoint M Z hM]

theorem logGram_rectLevi_nonneg {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    0 ≤ rectLevi logGram M Z := by
  rw [logGram_rectLevi_eq M Z hM]
  exact (RCLike.nonneg_iff.mp (Matrix.posSemidef_self_mul_conjTranspose
    (projectorTangent M Z)).trace_nonneg).1

theorem rowProjector_wirt_wirtBar {n m : ℕ} (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef) (i j : Fin m) :
    wirt (fun N : Rect n m => wirtBar (fun A : Rect n m => rowProjector A i j) N Z) M Z =
      ((projectorTangent M Z)ᴴ*projectorTangent M Z-
        projectorTangent M Z*(projectorTangent M Z)ᴴ) i j :=
  rowProjector_wirt_wirtBar_of_inverseGram M Z hM (inverseGram_differentiable_near M hM) i j

theorem projectorPenalty_rectLevi_computed {n m : ℕ} (P₀ : Herm m) (M Z : Rect n m)
    (hM : (M*Mᴴ).PosDef) :
    rectLevi (projectorPenalty (n := n) P₀) M Z =
      (Matrix.trace (P₀*(projectorTangent M Z*(projectorTangent M Z)ᴴ-
        (projectorTangent M Z)ᴴ*projectorTangent M Z))).re :=
  projectorPenalty_rectLevi P₀ M Z hM ((rowProjector_contDiffAt M hM).of_le (by simp))
    (inverseGram_differentiable_near M hM)

end Yau.NodeProofs.E02Aux
