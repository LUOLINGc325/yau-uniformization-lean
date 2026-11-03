import Yau.Proofs.F05DatumSourceBudget
import Yau.Proofs.F05PhysicalManifoldOperator
import Yau.Proofs.F05BootstrapNative

/-! The actual datum-subtracted equation in the full closed physical
chart retains every principal, drift, and prescribed time-jet term. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_dirichlet_relative_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p w : M.Carrier → ℝ → ℝ)
    (T : ℝ) (i : Fin A.count)
    (hp : C2 (F05Q A i T) (pull A i p)) (hw : C2 (F05Q A i T) (pull A i w))
    (hEquation : ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*scalarCurvature (h t) x) :
    ∀ z ∈ F05Q A i T,
      F05RelOp (region (A.normal i) 2) (Icc 0 T)
        (F05FlowPrincipal A i h (fun x t => Real.exp (-w x t)))
        (F05FlowDrift A i h (fun x t => Real.exp (-w x t)))
        (fun z => pull A i w z-pull A i p z) z =
      pull A i (F05DirichletForcing h T p w) z := by
  intro z hz
  let c : M.Carrier → ℝ → ℝ := fun x t => Real.exp (-w x t)
  rw [F05RelOp_eq_linearOp (F05_region_uniqueDiffOn (A.normal i) (by norm_num))
    (c2_sub hw hp) _ _ hz]
  change linearOp (F05Q A i T) (F05FlowPrincipal A i h c) (F05FlowDrift A i h c)
    (fun z => pull A i w z-pull A i p z) z = _
  rw [linearOp_sub hw hp hz]
  have hW := F05_intrinsic_operator_eq_chart hA h c T w i hz.1 (hw.2.2.2.2.1 z hz)
  have hP := F05_intrinsic_operator_eq_chart hA h c T p i hz.1 (hp.2.2.2.2.1 z hz)
  rw [← hW,← hP]
  have hEq := hEquation (lift A i z.1) (F05D_lift_mem_closure hA hz.1) z.2 hz.2
  unfold F05IntrinsicLinearOperator
  rw [hEq]
  dsimp only [c,pull,F05DirichletForcing]
  ring

end Yau.Proofs.F05Aux
