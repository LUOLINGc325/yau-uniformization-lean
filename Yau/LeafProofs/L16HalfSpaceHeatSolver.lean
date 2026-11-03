import Yau.LeafProofs.L16TraceNormalInvariance

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance halfSpaceHeatSolver_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceHeatSolver_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceHeatSolver_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceHeatSolver_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- Addition of actual parabolic C² functions preserves the full Schauder
    budget, without imposing Holder assumptions on lower jets. -/
theorem schauderBound_add {n : ℕ} {α C D : ℝ} {Q : Set (Point n)} {u v : Point n → ℝ}
    (hu : SchauderBound α Q u C) (hv : SchauderBound α Q v D) :
    SchauderBound α Q (fun p => u p+v p) (C+D) := by
  have hZero := c2_zero (n := n) Q
  have hn := c2_sub hZero hv.1
  have hD (p : Point n) (hp : p ∈ Q) :
      spatialD (fun p => u p+v p) p = spatialD u p+spatialD v p := by
    have hh := spatialD_sub hu.1 hn hp
    rw [spatialD_sub hZero hv.1 hp,spatialD_zero] at hh
    simpa only [zero_sub,sub_neg_eq_add] using hh
  have hDD (p : Point n) (hp : p ∈ Q) :
      spatialDD (fun p => u p+v p) p = spatialDD u p+spatialDD v p := by
    have hh := spatialDD_sub hu.1 hn hp
    rw [spatialDD_sub hZero hv.1 hp,spatialDD_zero] at hh
    simpa only [zero_sub,sub_neg_eq_add] using hh
  have ht (p : Point n) (hp : p ∈ Q) :
      timeD Q (fun p => u p+v p) p = timeD Q u p+timeD Q v p := by
    have hh := timeD_sub hu.1 hn hp
    rw [timeD_sub hZero hv.1 hp,timeD_zero] at hh
    simpa only [zero_sub,sub_neg_eq_add] using hh
  refine ⟨c2_add hu.1 hv.1,add_nonneg hu.2.1 hv.2.1,?_,
    holderBound_congr_on (holderBound_add hu.2.2.2.1 hv.2.2.2.1) (fun p hp => (hDD p hp).symm),
    holderBound_congr_on (holderBound_add hu.2.2.2.2 hv.2.2.2.2) (fun p hp => (ht p hp).symm)⟩
  intro p hp
  refine ⟨(abs_add_le _ _).trans (add_le_add (hu.2.2.1 p hp).1 (hv.2.2.1 p hp).1),?_⟩
  rw [hD p hp]
  exact (norm_add_le _ _).trans (add_le_add (hu.2.2.1 p hp).2 (hv.2.2.1 p hp).2)

/-- The true boundary trace heat layer, with its causal extension and actual
    second-order ambient reflection. -/
def halfSpaceTraceHeatDuhamel {n : ℕ} (e : Space n) (T : ℝ) (f : Point n → ℝ) : Point n → ℝ :=
  halfSpaceSecondOrderExtension e (boundaryTraceLayer e
    (tracePastExtension T (fun p => f (halfSpaceBoundaryProjection e p.1,p.2))))

/-- Only the first initial/lateral corner compatibility is required for the
    boundary trace part of the flat Dirichlet heat solver. -/
theorem halfSpace_trace_schauder_solution {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ T F : ℝ, 0 < T → T ≤ 1 →
      ∀ f : Point n → ℝ,
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x : Space n, inner ℝ e x = 0 → f (x,0) = 0) →
      let u := halfSpaceTraceHeatDuhamel e T f
      SchauderBound α (cylinder univ 0 T) u (C*F) ∧
      (∀ x : Space n, u (x,0) = 0) ∧
      (∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) ∧
      ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun _ => (1 : Mat n)) (fun _ _ => 0) u p =
          f (halfSpaceBoundaryProjection e p.1,p.2) := by
  obtain ⟨C,hC,hSolve⟩ := boundaryTraceLayer_extension_schauder (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro e he T F hT hT1 f hf hCompat
  let B := fun p : Point n => f (halfSpaceBoundaryProjection e p.1,p.2)
  let Bext := tracePastExtension T B
  have hB : HolderBound α (cylinder univ 0 T) B F := holderBound_halfSpace_boundary_trace hα.le hf
  have hBext : HolderBound α univ Bext F := tracePastExtension_holder hα.le hT.le hB
  have hB0 : ∀ x, B (x,0) = 0 := boundary_trace_initial_zero hCompat
  have hPast : ∀ y s, s ≤ 0 → Bext (y,s) = 0 :=
    fun y s hs => tracePastExtension_zero_past hB0 hs
  have hInv : ∀ (x : Space n) (c s : ℝ), Bext (x+c • e,s) = Bext (x,s) :=
    tracePastExtension_normal_invariant hT.le (fun x c s hs => boundary_trace_normal_invariant he f x c s)
  dsimp only
  refine ⟨hSolve e he T hT hT1 Bext F hBext hPast,?_,?_,?_⟩
  · intro x
    simp only [halfSpaceTraceHeatDuhamel,halfSpaceSecondOrderExtension,boundaryTraceLayer,
      normalTraceLayer_initial,mul_zero,sub_zero,add_zero,ite_self]
  · intro x hx t ht
    rw [halfSpaceTraceHeatDuhamel,halfSpaceSecondOrderExtension,ite_eq_left (by simpa only [hx] using le_refl (0 : ℝ))]
    change normalTraceLayer Bext (halfSpaceBoundaryProjection e x) t (inner ℝ e x) = 0
    rw [hx]
    exact normalTraceLayer_boundary Bext _ t
  · intro p hp
    rw [linearOp_cylinder_restrict_space (hp := hp)]
    exact (boundaryTraceLayer_extension_linearOp hα hα1 hT hT1 he hBext hPast hInv hp).trans
      (tracePastExtension_eqOn T B ⟨mem_univ _,hp.2⟩)

/-- Explicit flat Dirichlet heat solution: the genuine odd zero-trace residual
    plus the actual compatible boundary-trace layer. -/
def halfSpaceHeatDuhamel {n : ℕ} (e : Space n) (T : ℝ) (f : Point n → ℝ) : Point n → ℝ :=
  fun p => heatDuhamel (halfSpaceOddExtension e (halfSpaceZeroTraceResidual e f)) p.2 p.1+
    halfSpaceTraceHeatDuhamel e T f p

/-- The actual flat half-space heat solver has a full ambient Schauder bound,
    zero initial/lateral data, and the literal PDE, under first corner compatibility. -/
theorem halfSpace_heat_schauder_solution {n : ℕ} {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : Space n), ‖e‖ = 1 → ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x : Space n, inner ℝ e x = 0 → f (x,0) = 0) →
      let u := halfSpaceHeatDuhamel e T f
      SchauderBound α (cylinder univ 0 T) u (C*F) ∧
      (∀ x : Space n, u (x,0) = 0) ∧
      (∀ x : Space n, inner ℝ e x = 0 → ∀ t ∈ Icc 0 T, u (x,t) = 0) ∧
      ∀ p ∈ cylinder {x | 0 ≤ inner ℝ e x} 0 T,
        linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun _ => (1 : Mat n)) (fun _ _ => 0) u p = f p := by
  obtain ⟨CR,hCR,hHeat⟩ := heatDuhamel_schauder_solution (n := n) hα hα1
  obtain ⟨CT,hCT,hTrace⟩ := halfSpace_trace_schauder_solution (n := n) hα hα1
  refine ⟨4*CR+CT,by positivity,?_⟩
  intro e he T F hT hT1 f hf hCompat
  obtain ⟨CX,hCX,hResidual⟩ := halfSpace_zero_trace_residual_schauder_solution he hα hα1
  obtain ⟨_,hR0,hRB,hRPDE⟩ := hResidual T F hT hT1 f hf
  have hExt := holderBound_halfSpace_zero_trace_odd_extension he hα hf
  have hR := (hHeat T (4*F) hT hT1 _ hExt).1
  obtain ⟨hZ,hZ0,hZB,hZPDE⟩ := hTrace e he T F hT hT1 f hf hCompat
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · convert schauderBound_add hR hZ using 1 <;> try rfl
    ring
  · intro x
    simp only [halfSpaceHeatDuhamel]
    simpa only [add_zero] using congrArg₂ (fun a b : ℝ => a+b) (hR0 x) (hZ0 x)
  · intro x hx t ht
    simp only [halfSpaceHeatDuhamel]
    simpa only [add_zero] using congrArg₂ (fun a b : ℝ => a+b) (hRB x hx t ht) (hZB x hx t ht)
  · intro p hp
    change linearOp (cylinder {x | 0 ≤ inner ℝ e x} 0 T) (fun _ => (1 : Mat n)) (fun _ _ => 0)
      (fun q => heatDuhamel (halfSpaceOddExtension e (halfSpaceZeroTraceResidual e f)) q.2 q.1+
        halfSpaceTraceHeatDuhamel e T f q) p = f p
    rw [linearOp_add
      (c2_cylinder_restrict_space hR.1) (c2_cylinder_restrict_space hZ.1) hp,
      hRPDE p hp,hZPDE p hp]
    simp only [halfSpaceZeroTraceResidual,sub_add_cancel]

end Yau.LeafProofs.L16Aux
