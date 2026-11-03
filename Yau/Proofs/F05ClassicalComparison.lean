import Yau.Proofs.F05ReactionMaximum
import Yau.Proofs.F05ContinuousEllipticity
import Yau.Proofs.F05IntrinsicSub
import Yau.Proofs.F05ScalarRange

/-! Classical comparison on the original compact manifold domain uses the
actual scalar equation, without assuming either candidate nonnegative. -/

open Set
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_classical_comparison_bounded {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {T : ℝ} (hT : 0 < T)
    (hh : MetricFamilySmooth h (Icc 0 T)) (w u : M.Carrier → ℝ → ℝ)
    (hWCont : ContinuousOn (fun q : M.Carrier × ℝ => w q.1 q.2) (closure O ×ˢ Icc 0 T))
    (hUCont : ContinuousOn (fun q : M.Carrier × ℝ => u q.1 q.2) (closure O ×ˢ Icc 0 T))
    (hW : ∀ i, C2 (F05Q A i T) (pull A i w)) (hU : ∀ i, C2 (F05Q A i T) (pull A i u))
    (K A₀ : ℝ)
    (hLower : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, -K ≤ u x t)
    (hBound : ∀ x ∈ O, ∀ t ∈ Ioc 0 T,
      |scalarCurvature (h t) x-laplacian (h t) (fun y => u y t) x| ≤ A₀)
    (hInitial : ∀ x ∈ closure O, w x 0 ≤ u x 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t ≤ u x t)
    (hSub : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, derivWithin (w x) (Icc 0 T) t ≤
      scalarNonlinearRHS (scalarCurvature (h t) x) (laplacian (h t) (fun y => w y t) x) (w x t))
    (hSuper : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, scalarNonlinearRHS (scalarCurvature (h t) x)
      (laplacian (h t) (fun y => u y t) x) (u x t) ≤ derivWithin (u x) (Icc 0 T) t) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, w x t ≤ u x t := by
  let c := fun x t => Real.exp (-w x t)
  obtain ⟨lam,upper,hEll⟩ := F05_continuous_coefficient_elliptic hA h c hT.le hh
    (fun i => Real.continuous_exp.comp_continuousOn (hW i).1.neg) (fun _ _ _ => Real.exp_pos _)
  let d := fun x t => w x t-u x t
  have hDCont : ContinuousOn (fun q : M.Carrier × ℝ => d q.1 q.2) (closure O ×ˢ Icc 0 T) := hWCont.sub hUCont
  have hDC2 (i : Fin A.count) : C2 (F05Q A i T) (pull A i d) := c2_sub (hW i) (hU i)
  have hDInitial (x : M.Carrier) (hx : x ∈ closure O) : d x 0 ≤ 0 := sub_nonpos.mpr (hInitial x hx)
  have hDBoundary (x : M.Carrier) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 T) : d x t ≤ 0 :=
    sub_nonpos.mpr (hBoundary x hx t ht)
  have hDOp (x : M.Carrier) (hx : x ∈ O) (t : ℝ) (ht : t ∈ Ioc 0 T) (hPos : 0 < d x t) :
      F05IntrinsicLinearOperator c h T d x t ≤ (Real.exp K*A₀)*d x t := by
    have hWU : u x t ≤ w x t := by change 0 < w x t-u x t at hPos; linarith
    have hScalar := F05_scalar_rhs_sub_le_lower (scalarCurvature (h t) x)
      (laplacian (h t) (fun y => u y t) x) K A₀ (hLower x hx t ht) hWU (hBound x hx t ht)
    have hSubAt := hSub x hx t ht
    have hSuperAt := hSuper x hx t ht
    have hLinear := F05_intrinsic_operator_sub hA h c T w u hW hU (subset_closure hx) ⟨ht.1.le,ht.2⟩
    change F05IntrinsicLinearOperator c h T (fun x t => w x t-u x t) x t ≤ _
    rw [hLinear]
    unfold F05IntrinsicLinearOperator scalarNonlinearRHS at *
    dsimp only [c,d] at *
    linarith
  have hResult := F05_manifold_reaction_maximum hA h c hT d (Real.exp K*A₀) hDCont hDC2 hEll
    hDInitial hDBoundary hDOp
  intro x hx t ht
  exact sub_nonpos.mp (hResult x hx t ht)

end Yau.Proofs.F05Aux
