import Yau.Proofs.V02WallTaylorWithinJets

/-! Parameter jets on arbitrary joint domains that are open in the
parameter direction, including one-sided auxiliary time domains. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof

variable {E P F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_slice_of_mem_nhds {S : Set (E × P)} {f : E × P → F}
    {z : E} {p : P} (hf : DifferentiableWithinAt ℝ f S (z, p))
    (hs : {y : E | (y, p) ∈ S} ∈ 𝓝 z) :
    HasFDerivAt (fun y => f (y, p))
      ((fderivWithin ℝ f S (z, p)).comp (ContinuousLinearMap.inl ℝ E P)) z := by
  have hline : HasFDerivWithinAt (fun y : E => (y, p)) (ContinuousLinearMap.inl ℝ E P)
      {y : E | (y, p) ∈ S} z :=
    ((hasFDerivAt_id z).prodMk (hasFDerivAt_const p z)).hasFDerivWithinAt
  exact (hf.hasFDerivWithinAt.comp z hline (fun _ hy => hy)).hasFDerivAt hs

theorem parameterJetWithin_eq_iteratedFDeriv_of_slice {S : Set (E × P)}
    (hS : UniqueDiffOn ℝ S) {f : E × P → F} (hf : ContDiffOn ℝ ∞ f S)
    (hslice : ∀ w ∈ S, {y : E | (y, w.2) ∈ S} ∈ 𝓝 w.1)
    (m : ℕ) {z : E} {p : P} (hp : (z, p) ∈ S) :
    parameterJetWithin f S m (z, p) = iteratedFDeriv ℝ m (fun y => f (y, p)) z := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
    have hjet := parameterJetWithin_contDiffOn hS hf m
    have hder := (hasFDerivAt_slice_of_mem_nhds
      ((hjet.differentiableOn (by simp)) _ hp) (hslice _ hp)).fderiv
    have he : (fun y => parameterJetWithin f S m (y, p)) =ᶠ[𝓝 z]
        iteratedFDeriv ℝ m (fun y => f (y, p)) := by
      filter_upwards [hslice _ hp] with y hy
      exact ih hy
    change ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)
      ((fderivWithin ℝ (parameterJetWithin f S m) S (z, p)).comp (ContinuousLinearMap.inl ℝ E P)) =
      ContinuousLinearMap.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)
        (fderiv ℝ (iteratedFDeriv ℝ m (fun y => f (y, p))) z)
    rw [← hder]
    exact congrArg (fun L : E →L[ℝ] E [×m]→L[ℝ] F =>
      L.uncurryLeft (Ei := fun _ : Fin (m + 1) => E)) he.fderiv_eq

theorem exists_uniform_parameterJetWithin_bound {S : Set (E × P)} (hS : UniqueDiffOn ℝ S)
    {f : E × P → F} (hf : ContDiffOn ℝ ∞ f S)
    (hslice : ∀ w ∈ S, {y : E | (y, w.2) ∈ S} ∈ 𝓝 w.1)
    {K : Set (E × P)} (hK : IsCompact K) (hKS : K ⊆ S) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w ∈ K, ‖iteratedFDeriv ℝ m (fun z => f (z, w.2)) w.1‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn
    ((parameterJetWithin_contDiffOn hS hf m).continuousOn.mono hKS)).isBounded.exists_norm_le
  refine ⟨max B 0, le_max_right _ _, fun w hw => ?_⟩
  rw [← parameterJetWithin_eq_iteratedFDeriv_of_slice hS hf hslice m (hKS hw)]
  exact (hB _ ⟨w, hw, rfl⟩).trans (le_max_left _ _)

end Yau.Blueprint.V02WallTaylorProof
