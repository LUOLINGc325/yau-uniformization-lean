import Yau.Proofs.F01QuadraticJets

/-! A genuine quadratic holomorphic local chart with smooth inverse on its
entire open target. The source is restricted to the open invertible-derivative
locus, rather than extending a germwise inverse regularity claim. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem quadraticCoordinate_smooth_local_chart (B : E →L[ℂ] E →L[ℂ] E) :
    ∃ e : OpenPartialHomeomorph E E,
      (e : E → E) = quadraticCoordinate B ∧ (0 : E) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℂ ∞ e e.source ∧ ContDiffOn ℂ ∞ e.symm e.target := by
  obtain ⟨e0, he0, hs0, h00, _⟩ := quadraticCoordinate_local_inverse B
  let U : Set E := (fderiv ℂ (quadraticCoordinate B)) ⁻¹'
    range (fun L : E ≃L[ℂ] E => (L : E →L[ℂ] E))
  have hD : Continuous (fderiv ℂ (quadraticCoordinate B)) := by
    have he : fderiv ℂ (quadraticCoordinate B) =
        (fun z => ContinuousLinearMap.id ℂ E + (1 / 2 : ℂ) • (B z + B.flip z)) :=
      funext fun z => (quadraticCoordinate_hasFDerivAt B z).fderiv
    rw [he]
    fun_prop
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage hD
  have h0U : (0 : E) ∈ U := by
    change ∃ L : E ≃L[ℂ] E, (L : E →L[ℂ] E) = fderiv ℂ (quadraticCoordinate B) 0
    exact ⟨ContinuousLinearEquiv.refl ℂ E, (quadraticCoordinate_hasFDerivAt_zero B).fderiv.symm⟩
  let e := e0.restrOpen U hU
  have hef : (e : E → E) = quadraticCoordinate B := he0
  have hs : (0 : E) ∈ e.source := ⟨hs0, h0U⟩
  refine ⟨e, hef, hs, h00, ?_, ?_⟩
  · rw [hef]
    exact (quadraticCoordinate_contDiff B).contDiffOn
  · intro y hy
    have hx : e.symm y ∈ e.source := e.map_target hy
    have hxU : e.symm y ∈ U := hx.2
    obtain ⟨L, hL⟩ := hxU
    change (L : E →L[ℂ] E) = fderiv ℂ (quadraticCoordinate B) (e.symm y) at hL
    have hd : HasFDerivAt e (L : E →L[ℂ] E) (e.symm y) := by
      rw [hef, hL]
      exact ((quadraticCoordinate_contDiff B).differentiable (by simp) (e.symm y)).hasFDerivAt
    have hc : ContDiffAt ℂ ∞ e (e.symm y) := by
      rw [hef]
      exact (quadraticCoordinate_contDiff B).contDiffAt
    exact (e.contDiffAt_symm hy hd hc).contDiffWithinAt

end Yau.NodeProofs.F01Aux
