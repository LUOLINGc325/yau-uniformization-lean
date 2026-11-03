import Yau.Proofs.F04ScalarExteriorChain

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem realForm_eq_at_of_center_components (A B : RealForm M k) (x : M.Carrier)
    (h : ∀ I, formComponents A x (chartPt x x) I = formComponents B x (chartPt x x) I) :
    A x = B x := by
  apply sub_eq_zero.mp
  apply (formComponents_center_eq_zero_iff (A - B) x).mp
  funext I
  change formComponents A x (chartPt x x) I - formComponents B x (chartPt x x) I = 0
  rw [h I, sub_self]

/-- Local equality on an actual open set gives equality of the actual smooth
exterior differentials there. -/
theorem scalarExterior_congr_on_open {f v : M.Carrier → ℝ}
    (hf : SmoothFn f) (hv : SmoothFn v) (O : Set M.Carrier) (hO : IsOpen O)
    (he : EqOn f v O) (x : M.Carrier) (hx : x ∈ O) : scalarExterior f x = scalarExterior v x := by
  have ht : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hi : ContinuousAt (chartInv x) (chartPt x x) := continuousAt_extChartAt_symm'' ht
  have hinv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have ho : O ∈ 𝓝 (chartInv x (chartPt x x)) := by rw [hinv]; exact hO.mem_nhds hx
  have hc : inChart x f =ᶠ[𝓝 (chartPt x x)] inChart x v := by
    filter_upwards [hi.preimage_mem_nhds ho] with z hz
    exact he hz
  apply realForm_eq_at_of_center_components
  intro I
  rw [scalarExterior_components hf x ht I, scalarExterior_components hv x ht I]
  change fderiv ℝ (inChart x f) (chartPt x x) (realVec (I 0)) =
    fderiv ℝ (inChart x v) (chartPt x x) (realVec (I 0))
  rw [hc.fderiv_eq]

theorem scalarExterior_sub {f v : M.Carrier → ℝ} (hf : SmoothFn f) (hv : SmoothFn v) :
    scalarExterior (f - v) = scalarExterior f - scalarExterior v := by
  have hsub : SmoothFn (f - v) := fun c => (hf c).sub (hv c)
  apply realForm_eq_of_center_components
  intro x I
  have ht : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [scalarExterior_components hsub x ht I]
  change rDeriv (inChart x (f - v)) (chartPt x x) (I 0) =
    formComponents (scalarExterior f) x (chartPt x x) I -
      formComponents (scalarExterior v) x (chartPt x x) I
  rw [scalarExterior_components hf x ht I, scalarExterior_components hv x ht I]
  have hdf : DifferentiableAt ℝ (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds ht)).differentiableAt
      (by simp)
  have hdv : DifferentiableAt ℝ (inChart x v) (chartPt x x) :=
    ((hv x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds ht)).differentiableAt
      (by simp)
  change fderiv ℝ (inChart x f - inChart x v) (chartPt x x) (realVec (I 0)) =
    fderiv ℝ (inChart x f) (chartPt x x) (realVec (I 0)) -
      fderiv ℝ (inChart x v) (chartPt x x) (realVec (I 0))
  rw [(hdf.hasFDerivAt.sub hdv.hasFDerivAt).fderiv]
  rfl

end Yau.F04Proof
