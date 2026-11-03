import Yau.Proofs.F05IntrinsicClosedChartEquation
import Yau.Proofs.F05NonlinearTimePaste
import Yau.Proofs.F05PhysicalSchauderPaste

/-! Actual physical traces suffice to paste two solutions of the original
manifold equation. The equation determines the joining time jet. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.LeafProofs.L16BoundaryTimeAux
variable {n : ℕ} {M : ComplexManifold n}

def F05ManifoldTimePaste (τ : ℝ) (u v : M.Carrier → ℝ → ℝ) : M.Carrier → ℝ → ℝ :=
  fun x t => if t ≤ τ then u x t else v x t

theorem F05_manifold_nonlinear_paste {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M)
    {τ T α C D : ℝ} (hτ : 0 < τ) (hτT : τ < T) (hα : 0 < α)
    (u v : M.Carrier → ℝ → ℝ)
    (hu : ∀ i, SchauderBound α (cylinder (F05D A i) 0 τ) (pull A i u) C)
    (hv : ∀ i, SchauderBound α (cylinder (F05D A i) τ T) (pull A i v) D)
    (hTrace : ∀ x ∈ closure O, u x τ = v x τ)
    (hUEq : ∀ x ∈ closure O, ∀ t ∈ Icc 0 τ,
      derivWithin (u x) (Icc 0 τ) t = Real.exp (-u x t)*laplacian (h t) (fun y => u y t) x+
        (1-Real.exp (-u x t))*scalarCurvature (h t) x)
    (hVEq : ∀ x ∈ closure O, ∀ t ∈ Icc τ T,
      derivWithin (v x) (Icc τ T) t = Real.exp (-v x t)*laplacian (h t) (fun y => v y t) x+
        (1-Real.exp (-v x t))*scalarCurvature (h t) x) :
    (∀ i, SchauderBound α (F05Q A i T) (pull A i (F05ManifoldTimePaste τ u v)) (2*(C+D))) ∧
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (F05ManifoldTimePaste τ u v x) (Icc 0 T) t =
        Real.exp (-F05ManifoldTimePaste τ u v x t)*
          laplacian (h t) (fun y => F05ManifoldTimePaste τ u v y t) x+
        (1-Real.exp (-F05ManifoldTimePaste τ u v x t))*scalarCurvature (h t) x := by
  have hU i := F05_closed_nonlinear_chart_equation hA h u i (hu i).1 hUEq
  have hV i := F05_closed_nonlinear_chart_equation hA h v i (hv i).1 hVEq
  have hTr (i : Fin A.count) (x : Space n) (hx : x ∈ F05D A i) :
      pull A i u (x,τ) = pull A i v (x,τ) := hTrace _ (F05D_lift_mem_closure hA hx)
  have hTime (i : Fin A.count) (x : Space n) (hx : x ∈ F05D A i) :
      timeD (cylinder (F05D A i) 0 τ) (pull A i u) (x,τ) =
        timeD (cylinder (F05D A i) τ T) (pull A i v) (x,τ) := by
    have hSpatial := F05_physical_trace_spatial_jets
      (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 2))
      (pull A i u) (pull A i v) τ
      (fun x hx => (hu i).1.2.2.2.2.1 (x,τ) ⟨hx,hτ.le,le_rfl⟩)
      (fun x hx => (hv i).1.2.2.2.2.1 (x,τ) ⟨hx,le_rfl,hτT.le⟩) (hTr i) x hx
    rw [hU i (x,τ) ⟨hx,hτ.le,le_rfl⟩,hV i (x,τ) ⟨hx,le_rfl,hτT.le⟩,
      hTr i x hx,hSpatial.1,hSpatial.2]
  have hSch (i : Fin A.count) :
      SchauderBound α (F05Q A i T) (pull A i (F05ManifoldTimePaste τ u v)) (2*(C+D)) :=
    F05_schauder_timePaste_physical (F05_region_isClosed (A.normal i) 2)
      (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 2))
      hτ hτT hα (hu i) (hv i) (hTr i) (hTime i)
  refine ⟨hSch,F05_intrinsic_nonlinear_of_closed_charts hA h _ (fun i => (hSch i).1) ?_⟩
  intro i z hz
  exact (F05_nonlinear_timePaste_physical (F05_region_isClosed (A.normal i) 2)
    (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 2)) hτ hτT
    (pull A i u) (pull A i v) (fun q => flatA (h q.2) A i q)
    (fun q => flatB (h q.2) A i q) (fun q => scalarCurvature (h q.2) (lift A i q.1))
    (hu i).1 (hv i).1 (hTr i) (hU i) (hV i)).2 z hz

end Yau.Proofs.F05Aux
