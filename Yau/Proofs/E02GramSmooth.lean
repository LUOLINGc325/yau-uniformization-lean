import Yau.Proofs.E02GramRegularity
import Yau.Proofs.E02InverseDerivative
import Yau.LeafProofs.L07

open Matrix Set Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inverseGram_contDiffOn (n m : ℕ) :
    ContDiffOn ℝ ∞ (fun M : Rect n m => (M*Mᴴ)⁻¹) (fullRankRect n m) :=
  Yau.LeafProofs.L07Aux.matrix_inv_contDiffOn _ (gram_contDiff n m).contDiffOn (fun _ hM => hM)

theorem inverseGram_contDiffAt {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    ContDiffAt ℝ ∞ (fun N : Rect n m => (N*Nᴴ)⁻¹) M :=
  (inverseGram_contDiffOn n m).contDiffAt
    ((isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM))

theorem inverseGram_differentiable_near {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    ∀ᶠ N in 𝓝 M, DifferentiableAt ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) N := by
  filter_upwards [(isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM)] with N hN
  exact (inverseGram_contDiffAt N ((fullRankRect_iff_posDef N).mp hN)).differentiableAt (by simp)

/-- Actual inverse smoothness discharges the prior ordinary inverse
calculus input on the genuine open full-rank locus. -/
theorem inverseGram_fderiv_apply {n m : ℕ} (M Z : Rect n m) (hM : (M*Mᴴ).PosDef) :
    fderiv ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M Z =
      -((M*Mᴴ)⁻¹*(M*Zᴴ+Z*Mᴴ)*(M*Mᴴ)⁻¹) := by
  have hNear : ∀ᶠ N in 𝓝 M, IsUnit (N*Nᴴ).det := by
    filter_upwards [(isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM)] with N hN
    exact isUnit_iff_ne_zero.mpr hN
  have h := matrix_inv_fderiv_apply (fun N : Rect n m => N*Nᴴ) M Z
    (gram_hasFDerivAt M).differentiableAt
    ((inverseGram_contDiffAt M hM).differentiableAt (by simp)) hNear
  change fderiv ℝ (fun N : Rect n m => (N*Nᴴ)⁻¹) M Z =
    -((M*Mᴴ)⁻¹*fderiv ℝ (fun N : Rect n m => N*Nᴴ) M Z*(M*Mᴴ)⁻¹) at h
  simpa only [gram_fderiv,gramHessian_apply] using h

theorem rowProjector_contDiffOn (n m : ℕ) :
    ContDiffOn ℝ ∞ (rowProjector (n := n) (m := m)) (fullRankRect n m) := by
  have hAdj : ContDiffOn ℝ ∞ (fun M : Rect n m => Mᴴ) (fullRankRect n m) :=
    (rectAdjointCLM n m).contDiff.contDiffOn
  have hLeft := ((rectMulCLM m n n).contDiff.comp_contDiffOn hAdj).clm_apply
    (inverseGram_contDiffOn n m)
  exact ((rectMulCLM m n m).contDiff.comp_contDiffOn hLeft).clm_apply contDiffOn_id

theorem rowProjector_contDiffAt {n m : ℕ} (M : Rect n m) (hM : (M*Mᴴ).PosDef) :
    ContDiffAt ℝ ∞ (rowProjector (n := n) (m := m)) M :=
  (rowProjector_contDiffOn n m).contDiffAt
    ((isOpen_fullRankRect n m).mem_nhds ((fullRankRect_iff_posDef M).mpr hM))

end Yau.NodeProofs.E02Aux
