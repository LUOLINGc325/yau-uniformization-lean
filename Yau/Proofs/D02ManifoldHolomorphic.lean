import Yau.Proofs.D02Pullback
import Yau.Proofs.B01Coordinate

/-! A genuinely holomorphic map from a complex curve supplies the analytic
base map needed by the actual complex pullback-bundle construction. -/

open scoped Manifold Topology ContDiff

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

/-- The one-dimensional model version includes analytic order, not only C∞. -/
theorem holomorphic_curve_contDiffOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {U : Set (ComplexVector 1)}
    {f : ComplexVector 1 → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    ContDiffOn ℂ ⊤ f U := by
  let e : ℂ ≃L[ℂ] ComplexVector 1 :=
    Yau.Proofs.B01Aux.complexOneEquiv.toContinuousLinearEquiv
  have hd : DifferentiableOn ℂ (f ∘ e) (e ⁻¹' U) :=
    hf.comp e.differentiable.differentiableOn (fun _ hz => hz)
  have ha : ContDiffOn ℂ ⊤ (f ∘ e) (e ⁻¹' U) :=
    hd.contDiffOn (hU.preimage e.continuous)
  have ht : ContDiffOn ℂ ⊤ (fun z => f (e (e.symm z))) U :=
    ha.comp e.symm.contDiff.contDiffOn (fun z hz => by
      simpa only [Set.mem_preimage, e.apply_symm_apply] using hz)
  simpa only [e.apply_symm_apply] using ht

theorem holomorphic_curve_contMDiff {n : ℕ} {B : ComplexManifold 1}
    {M : ComplexManifold n} {f : B.Carrier → M.Carrier}
    (hf : MDifferentiable (ComplexModel 1) (ComplexModel n) f) :
    ContMDiff (ComplexModel 1) (ComplexModel n) ⊤ f := by
  refine contMDiff_iff.mpr ⟨hf.continuous, fun x y => ?_⟩
  apply holomorphic_curve_contDiffOn ((mdifferentiable_iff.mp hf).2 x y)
  exact (hf.continuous.comp_continuousOn
    (continuousOn_extChartAt_symm (I := ComplexModel 1) x)).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := ComplexModel 1) x)
      (isOpen_extChartAt_source (I := ComplexModel n) y)

/-- This constructor consumes just the original holomorphic-map predicate. -/
def holomorphicCurveMap {n : ℕ} {B : ComplexManifold 1} {M : ComplexManifold n}
    (f : B.Carrier → M.Carrier)
    (hf : MDifferentiable (ComplexModel 1) (ComplexModel n) f) :
    ContMDiffMap (ComplexModel 1) (ComplexModel n) B.Carrier M.Carrier ⊤ :=
  ⟨f, holomorphic_curve_contMDiff hf⟩

@[simp] theorem holomorphicCurveMap_apply {n : ℕ} {B : ComplexManifold 1}
    {M : ComplexManifold n} (f : B.Carrier → M.Carrier)
    (hf : MDifferentiable (ComplexModel 1) (ComplexModel n) f) (x : B.Carrier) :
    holomorphicCurveMap f hf x = f x := rfl

end Yau.NodeProofs.D02Aux
