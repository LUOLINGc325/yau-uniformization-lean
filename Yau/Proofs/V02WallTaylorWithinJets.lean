import Yau.Proofs.V03PartialDerivative

/-! Actual parameter jets computed with joint within derivatives. Auxiliary
parameters may lie at the endpoint of a closed time interval. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open V03Proof

variable {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def parameterJetWithin (f : E × P → F) (S : Set (E × P)) :
    (m : ℕ) → E × P → E [×m]→L[ℝ] F
  | 0 => fun p => ContinuousMultilinearMap.uncurry0 ℝ E (f p)
  | m + 1 => fun p => ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)
      ((fderivWithin ℝ (parameterJetWithin f S m) S p).comp (ContinuousLinearMap.inl ℝ E P))

theorem parameterJetWithin_contDiffOn {S : Set (E × P)} (hS : UniqueDiffOn ℝ S)
    {f : E × P → F} (hf : ContDiffOn ℝ ∞ f S) (m : ℕ) :
    ContDiffOn ℝ ∞ (parameterJetWithin f S m) S := by
  induction m with
  | zero => exact (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp_contDiffOn hf
  | succ m ih =>
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).symm.contDiff.comp_contDiffOn
      ((ih.fderivWithin hS (m := ∞) (by simp)).clm_comp contDiffOn_const)

theorem parameterJetWithin_eq_iteratedFDeriv {U : Set E} (hU : IsOpen U)
    {J : Set P} (hJ : UniqueDiffOn ℝ J) {f : E × P → F}
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ J)) (m : ℕ) {z : E} {p : P}
    (hz : z ∈ U) (hp : p ∈ J) :
    parameterJetWithin f (U ×ˢ J) m (z, p) = iteratedFDeriv ℝ m (fun y => f (y, p)) z := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
    have hjet := parameterJetWithin_contDiffOn (hU.uniqueDiffOn.prod hJ) hf m
    have hder := (hasFDerivAt_spatial_slice hU hz hp
      ((hjet.differentiableOn (by simp)) _ ⟨hz, hp⟩)).fderiv
    have hinl : (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] P) =
        ContinuousLinearMap.inl ℝ E P := by ext x <;> rfl
    rw [hinl] at hder
    have he : (fun y => parameterJetWithin f (U ×ˢ J) m (y, p)) =ᶠ[𝓝 z]
        iteratedFDeriv ℝ m (fun y => f (y, p)) := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact ih hy
    change ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)
      ((fderivWithin ℝ (parameterJetWithin f (U ×ˢ J) m) (U ×ˢ J) (z, p)).comp
        (ContinuousLinearMap.inl ℝ E P)) =
      ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)
        (fderiv ℝ (iteratedFDeriv ℝ m (fun y => f (y, p))) z)
    rw [← hder]
    exact congrArg (fun L : E →L[ℝ] E [×m]→L[ℝ] F =>
      L.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)) he.fderiv_eq

end Yau.Blueprint.V02WallTaylorProof
