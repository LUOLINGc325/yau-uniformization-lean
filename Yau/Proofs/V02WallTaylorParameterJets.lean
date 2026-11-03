import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual parameter jets, retaining auxiliary variables. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

variable {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual ambient derivatives restricted to the parameter directions. -/
def parameterJet (f : E × P → F) : (m : ℕ) → E × P → E [×m]→L[ℝ] F
  | 0 => fun p => ContinuousMultilinearMap.uncurry0 ℝ E (f p)
  | m + 1 => fun p => ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)
      ((fderiv ℝ (parameterJet f m) p).comp (ContinuousLinearMap.inl ℝ E P))

theorem parameterJet_contDiffOn {Ω : Set (E × P)} (hΩ : IsOpen Ω)
    {f : E × P → F} (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ContDiffOn ℝ ∞ (parameterJet f m) Ω := by
  induction m with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp_contDiffOn hf
  | succ m ih =>
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).symm.contDiff.comp_contDiffOn
      ((ih.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_comp contDiffOn_const)

theorem parameterJet_eq_iteratedFDeriv {Ω : Set (E × P)} (hΩ : IsOpen Ω)
    {f : E × P → F} (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ)
    {z : E} {p : P} (hp : (z, p) ∈ Ω) :
    parameterJet f m (z, p) = iteratedFDeriv ℝ m (fun y => f (y, p)) z := by
  induction m generalizing z p with
  | zero => rfl
  | succ m ih =>
    have hd := (((parameterJet_contDiffOn hΩ hf m).contDiffAt
      (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
    have hlin : HasFDerivAt (fun y : E => (y, p)) (ContinuousLinearMap.inl ℝ E P) z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const p z)
    have hder := (hd.comp z hlin).fderiv
    have he : (fun y => parameterJet f m (y, p)) =ᶠ[𝓝 z]
        iteratedFDeriv ℝ m (fun y => f (y, p)) := by
      have hne : {y : E | (y, p) ∈ Ω} ∈ 𝓝 z :=
        (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hp)
      filter_upwards [hne] with y hy
      exact ih hy
    change ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)
      ((fderiv ℝ (parameterJet f m) (z, p)).comp (ContinuousLinearMap.inl ℝ E P)) =
        ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (m + 1) => E) (fderiv ℝ (iteratedFDeriv ℝ m (fun y => f (y, p))) z)
    rw [← hder]
    exact congrArg (fun L : E →L[ℝ] E [×m]→L[ℝ] F =>
      L.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)) he.fderiv_eq

end Yau.Blueprint.V02WallTaylorProof
