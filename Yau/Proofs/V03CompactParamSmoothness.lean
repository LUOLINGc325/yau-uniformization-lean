import Yau.Proofs.V03CompactParamTrace

/-! Genuine joint smoothness yields smooth dependence in the uniform
compact-trace norm. The proof differentiates the actual trace and iterates
through native continuous-linear-map derivative spaces. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof

universe u

theorem compactParamTrace_contDiffOn {P Q F : Type u}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set P} (hU : IsOpen U) {J : Set Q} [CompactSpace J]
    (hJU : UniqueDiffOn ℝ J) {f : P × Q → F} (hf : ContDiffOn ℝ ∞ f (U ×ˢ J)) :
    ContDiffOn ℝ ∞ (compactParamTrace hf.continuousOn) U := by
  have hUJ : UniqueDiffOn ℝ (U ×ˢ J) := hU.uniqueDiffOn.prod hJU
  have hnat : ∀ m : ℕ, ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V],
      ∀ (g : P × Q → V) (hg : ContDiffOn ℝ ∞ g (U ×ˢ J)),
        ContDiffOn ℝ m (compactParamTrace hg.continuousOn) U := by
    intro m
    induction m with
    | zero =>
        intro V _ _ g hg
        exact contDiffOn_zero.mpr (compactParamTrace_continuousOn hg.continuousOn)
    | succ m ih =>
        intro V _ _ g hg
        let D : P × Q → P →L[ℝ] V := spatialParameterDerivative g U J
        have hD : ContDiffOn ℝ ∞ D (U ×ˢ J) := spatialParameterDerivative_contDiffOn hUJ hg
        have htrace : ContDiffOn ℝ m (compactParamTrace hD.continuousOn) U := ih _ D hD
        have hder : ∀ p ∈ U, ∀ k : J,
            HasFDerivAt (fun y => compactParamTrace hg.continuousOn y k)
              (compactParamTrace hD.continuousOn p k) p := by
          intro p hp k
          rw [compactParamTrace_apply hD.continuousOn hp k]
          exact compactParamTrace_pointwise_hasFDerivAt hU hg hp k
        exact contDiffOn_continuousMap_succ hU m htrace hder
  exact contDiffOn_infty.mpr (fun m => hnat m F f hf)

end Yau.Blueprint.V03Proof
