import Yau.Proofs.P03SectionArrays
import Yau.Proofs.P03ContinuousCR

open scoped Manifold Topology ContDiff
open Set MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Zero extension is used only to write integrals; its values on the
closed coordinate ball retain the original continuous coefficient. -/
def compactBallExtension {F : Type*} [TopologicalSpace F] [Zero F] (a : M.Carrier) (r : ℝ)
    (b : C(chartClosedBall a r, F)) (z : ComplexVector n) : F := by
  classical
  exact if hz : z ∈ chartClosedBall a r then b ⟨z, hz⟩ else 0

theorem compactBallExtension_continuousOn {F : Type*} [TopologicalSpace F] [Zero F]
    (a : M.Carrier) (r : ℝ) (b : C(chartClosedBall a r, F)) :
    ContinuousOn (compactBallExtension a r b) (chartClosedBall a r) := by
  classical
  have heq : (chartClosedBall a r).domRestrict (compactBallExtension a r b) =
      (b : chartClosedBall a r → F) := by
    funext z
    exact dif_pos z.2
  rw [continuousOn_iff_continuous_domRestrict, heq]
  exact b.continuous

theorem compactBallCRTestCLM_apply_extension (a : M.Carrier) (r : ℝ) (α i : Fin n)
    (ψ : ComplexVector n → ℂ) (hψ : ContDiff ℝ ∞ ψ)
    (b : C(chartClosedBall a r, ComplexVector n)) :
    compactBallCRTestCLM a r α i ψ hψ b =
      ∫ z, compactBallExtension a r b z α * wirtBar ψ z (stdVec i) ∂lebesgueC n := by
  classical
  unfold compactBallCRTestCLM
  rw [ContinuousLinearMap.comp_apply, compactPairingCLM_apply]
  change (∫ z : chartClosedBall a r, wirtBar ψ z (stdVec i) * b z α
    ∂volume.comap (Subtype.val : chartClosedBall a r → ComplexVector n)) = _
  have hrestrict : (fun z : chartClosedBall a r => wirtBar ψ z (stdVec i) * b z α) =
      (fun z : chartClosedBall a r =>
        compactBallExtension a r b z α * wirtBar ψ z (stdVec i)) := by
    funext z
    simp only [compactBallExtension, dif_pos z.2, mul_comm]
  rw [hrestrict, integral_subtype_comap (s := chartClosedBall a r)
    Metric.isClosed_closedBall.measurableSet
    (fun z => compactBallExtension a r b z α * wirtBar ψ z (stdVec i)),
    ← actualMeasure_eq_volume n]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  simp only [compactBallExtension, dif_neg hz, PiLp.zero_apply, zero_mul]

theorem CRSectionArrays_holomorphic_extension {ι : Type*}
    (a : ι → M.Carrier) (r : ι → ℝ) (b : closedSectionArrays a r) (j : ι) :
    DifferentiableOn ℂ (compactBallExtension (a j) (r j) (b.1 j))
      (Metric.ball (chartPt (a j) (a j)) (r j)) := by
  have htests : ∀ (j : ι) (α i : Fin n) (ψ : ComplexVector n → ℂ)
      (hψ : ContDiff ℝ ∞ ψ) (_ : HasCompactSupport ψ)
      (_ : tsupport ψ ⊆ Metric.ball (chartPt (a j) (a j)) (r j)),
      sectionArrayCRTestCLM a r j α i ψ hψ b.1 = 0 := by
    have hm := b.2.2
    simp only [CRSectionArrays, Submodule.coe_iInf, Set.mem_iInter] at hm
    intro j α i ψ hψ hc hs
    exact LinearMap.mem_ker.mp (hm j α i ψ hψ hc hs)
  apply (differentiableOn_piLp 2).mpr
  intro α
  have hc : ContinuousOn (fun z => compactBallExtension (a j) (r j) (b.1 j) z α)
      (Metric.ball (chartPt (a j) (a j)) (r j)) :=
    ((EuclideanSpace.proj α).continuous.comp_continuousOn
      (compactBallExtension_continuousOn (a j) (r j) (b.1 j))).mono
        Metric.ball_subset_closedBall
  apply (continuous_holomorphic_iff_weakCR Metric.isOpen_ball hc).mpr
  intro i ψ hψ hcomp hs
  rw [← compactBallCRTestCLM_apply_extension (a j) (r j) α i ψ hψ (b.1 j)]
  exact htests j α i ψ hψ hcomp hs

end Yau.NodeProofs.P03Aux
