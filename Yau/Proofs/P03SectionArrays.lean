import Yau.Proofs.P03CompactPairing
import Yau.Proofs.P03CompactChartCover
import Yau.LeafProofs.L14

open scoped Manifold Topology ContDiff
open Set MeasureTheory TopologicalSpace

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L14Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}

abbrev chartClosedBall (a : M.Carrier) (r : ℝ) :=
  Metric.closedBall (chartPt a a) r

/-- Coordinates on actual compact chart balls, with the product of their
compact-convergence uniformities. -/
abbrev SectionArrays (a : ι → M.Carrier) (r : ι → ℝ) :=
  ∀ i, C(chartClosedBall (a i) (r i), ComplexVector n)

def sectionArrayOverlapCLM (a : ι → M.Carrier) (r : ι → ℝ)
    (i j : ι) (x : M.Carrier)
    (hi : chartPt (a i) x ∈ chartClosedBall (a i) (r i))
    (hj : chartPt (a j) x ∈ chartClosedBall (a j) (r j)) :
    SectionArrays a r →L[ℂ] TangentVector M x :=
  (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) (a i)).symm
    (chartPt (a i) x)).comp
      ((ContinuousMap.evalCLM (R := ℂ) ⟨chartPt (a i) x, hi⟩).comp
        (ContinuousLinearMap.proj i)) -
  (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) (a j)).symm
    (chartPt (a j) x)).comp
      ((ContinuousMap.evalCLM (R := ℂ) ⟨chartPt (a j) x, hj⟩).comp
        (ContinuousLinearMap.proj j))

def compactBallCRTestCLM (a : M.Carrier) (r : ℝ) (α i : Fin n)
    (ψ : ComplexVector n → ℂ) (hψ : ContDiff ℝ ∞ ψ) :
    C(chartClosedBall a r, ComplexVector n) →L[ℂ] ℂ := by
  let K := chartClosedBall a r
  let μ : Measure K := volume.comap (Subtype.val : K → ComplexVector n)
  letI : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe Metric.isClosed_closedBall.measurableSet)
  let w : C(K, ℂ) := ⟨fun z => wirtBar ψ z (stdVec i),
    (wirtBar_contDiff ψ hψ (stdVec i)).continuous.comp continuous_subtype_val⟩
  let I : C(K, ℂ) →L[ℂ] ℂ := compactPairingCLM μ (ContinuousMap.id K) w
  let P : C(K, ComplexVector n) →L[ℂ] C(K, ℂ) :=
    ContinuousLinearMap.compLeftContinuous ℂ K (EuclideanSpace.proj α)
  exact I.comp P

def sectionArrayCRTestCLM (a : ι → M.Carrier) (r : ι → ℝ) (j : ι) (α i : Fin n)
    (ψ : ComplexVector n → ℂ) (hψ : ContDiff ℝ ∞ ψ) :
    SectionArrays a r →L[ℂ] ℂ :=
  (compactBallCRTestCLM (a j) (r j) α i ψ hψ).comp (ContinuousLinearMap.proj j)

/-- Actual overlap equalities in intrinsic tangent fibres. Source membership
is retained, so no identity is imposed on arbitrary off-chart extensions. -/
def compatibleSectionArrays (a : ι → M.Carrier) (r : ι → ℝ) :
    Submodule ℂ (SectionArrays a r) :=
  ⨅ (i : ι) (j : ι) (x : M.Carrier)
    (_ : x ∈ (extChartAt (ComplexModel n) (a i)).source)
    (_ : x ∈ (extChartAt (ComplexModel n) (a j)).source)
    (hi : chartPt (a i) x ∈ chartClosedBall (a i) (r i))
    (hj : chartPt (a j) x ∈ chartClosedBall (a j) (r j)),
    (sectionArrayOverlapCLM a r i j x hi hj).ker

/-- The original weak CR equations on the interior of each coordinate ball. -/
def CRSectionArrays (a : ι → M.Carrier) (r : ι → ℝ) :
    Submodule ℂ (SectionArrays a r) :=
  ⨅ (j : ι) (α : Fin n) (i : Fin n) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (_ : HasCompactSupport ψ)
    (_ : tsupport ψ ⊆ Metric.ball (chartPt (a j) (a j)) (r j)),
    (sectionArrayCRTestCLM a r j α i ψ hψ).ker

def closedSectionArrays (a : ι → M.Carrier) (r : ι → ℝ) :
    Submodule ℂ (SectionArrays a r) :=
  compatibleSectionArrays a r ⊓ CRSectionArrays a r

theorem isClosed_iInf_submodule {A : Type*} [AddCommGroup A] [Module ℂ A]
    [TopologicalSpace A] {J : Sort*} (S : J → Submodule ℂ A)
    (hS : ∀ j, IsClosed (S j : Set A)) :
    IsClosed (((⨅ j, S j) : Submodule ℂ A) : Set A) := by
  rw [Submodule.coe_iInf]
  exact isClosed_iInter hS

theorem compatibleSectionArrays_isClosed (a : ι → M.Carrier) (r : ι → ℝ) :
    IsClosed (compatibleSectionArrays a r : Set (SectionArrays a r)) := by
  unfold compatibleSectionArrays
  repeat' (apply isClosed_iInf_submodule; intro)
  exact ContinuousLinearMap.isClosed_ker _

theorem CRSectionArrays_isClosed (a : ι → M.Carrier) (r : ι → ℝ) :
    IsClosed (CRSectionArrays a r : Set (SectionArrays a r)) := by
  unfold CRSectionArrays
  repeat' (apply isClosed_iInf_submodule; intro)
  exact ContinuousLinearMap.isClosed_ker _

theorem closedSectionArrays_isClosed (a : ι → M.Carrier) (r : ι → ℝ) :
    IsClosed (closedSectionArrays a r : Set (SectionArrays a r)) :=
  (compatibleSectionArrays_isClosed a r).inter (CRSectionArrays_isClosed a r)

theorem sectionArrays_complete (a : ι → M.Carrier) (r : ι → ℝ) :
    CompleteSpace (SectionArrays a r) := by
  infer_instance

theorem sectionArrays_completelyMetrizable [Countable ι]
    (a : ι → M.Carrier) (r : ι → ℝ) :
    IsCompletelyMetrizableSpace (SectionArrays a r) := by
  infer_instance

theorem closedSectionArrays_complete (a : ι → M.Carrier) (r : ι → ℝ) :
    CompleteSpace (closedSectionArrays a r) :=
  (closedSectionArrays_isClosed a r).isComplete.completeSpace_coe

theorem closedSectionArrays_baire [Countable ι]
    (a : ι → M.Carrier) (r : ι → ℝ) : BaireSpace (closedSectionArrays a r) := by
  letI := sectionArrays_completelyMetrizable a r
  letI := (closedSectionArrays_isClosed a r).isCompletelyMetrizableSpace
  infer_instance

end Yau.NodeProofs.P03Aux
