import Yau.Proofs.F04EnergyRepresentatives

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

theorem scalarExterior_scalar_comp {n : ℕ} {M : ComplexManifold n}
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) :
    scalarExterior (fun x => β (f x)) =
      multiplyRealForm (fun x => deriv β (f x)) (scalarExterior f) := by
  have hcomp : SmoothFn (fun x => β (f x)) := fun c => hβ.comp_contDiffOn (hf c)
  apply realForm_eq_of_center_components
  intro x I
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [scalarExterior_components hcomp x hx I,
    formComponents_multiplyRealForm, scalarExterior_components hf x hx I]
  have hdf : DifferentiableAt ℝ (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hx)).differentiableAt
      (by simp)
  have hreal : HasFDerivAt (fun z => β ((inChart x f) z))
      (deriv β ((inChart x f) (chartPt x x)) • fderiv ℝ (inChart x f) (chartPt x x)) (chartPt x x) :=
    ((hβ.differentiable (by simp) _).hasDerivAt).comp_hasFDerivAt _ hdf.hasFDerivAt
  change fderiv ℝ (fun z => β ((inChart x f) z)) (chartPt x x) (realVec (I 0)) =
    deriv β ((inChart x f) (chartPt x x)) * fderiv ℝ (inChart x f) (chartPt x x) (realVec (I 0))
  simp only [hreal.fderiv, smul_apply, smul_eq_mul]

end Yau.F04Proof
