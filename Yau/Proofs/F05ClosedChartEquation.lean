import Yau.Proofs.F05FlattenedLaplacian

/-! Exact equivalence of the original nonlinear equation and its actual
flattened equation on any closed time slab, including both time faces. -/

open Set
noncomputable section
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_timeD_pull_interval (A : AtlasData M) (i : Fin A.count) (l r : ℝ)
    (w : M.Carrier → ℝ → ℝ) {p : Point n} (hp : p.1 ∈ F05D A i) :
    timeD (cylinder (F05D A i) l r) (pull A i w) p =
      derivWithin (w (lift A i p.1)) (Icc l r) p.2 := by
  have hFiber : {t | (p.1,t) ∈ cylinder (F05D A i) l r} = Icc l r := by
    ext t
    change (p.1 ∈ F05D A i ∧ t ∈ Icc l r) ↔ t ∈ Icc l r
    exact and_iff_right hp
  unfold timeD
  rw [hFiber]
  rfl

theorem F05_closed_nonlinear_chart_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (w : M.Carrier → ℝ → ℝ)
    {l r : ℝ} (i : Fin A.count) (hw : C2 (cylinder (F05D A i) l r) (pull A i w))
    (hEq : ∀ x ∈ closure O, ∀ t ∈ Icc l r,
      derivWithin (w x) (Icc l r) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*scalarCurvature (h t) x) :
    ∀ z ∈ cylinder (F05D A i) l r,
      timeD (cylinder (F05D A i) l r) (pull A i w) z = Real.exp (-pull A i w z)*
        ((∑ a,∑ b,flatA (h z.2) A i z a b*spatialDD (pull A i w) z (realVec a) (realVec b))+
          ∑ a,flatB (h z.2) A i z a*spatialD (pull A i w) z (realVec a))+
        (1-Real.exp (-pull A i w z))*scalarCurvature (h z.2) (lift A i z.1) := by
  intro z hz
  have hLap := F05_flattened_laplacian_C2 hA (h z.2) i (fun x => w x z.2)
    (F05D_mem_ball hz.1) (hw.2.2.2.2.1 z hz)
  rw [F05_timeD_pull_interval A i l r w hz.1,
    hEq (lift A i z.1) (F05D_lift_mem_closure hA hz.1) z.2 hz.2,hLap]
  rfl


end Yau.Proofs.F05Aux
