import Yau.Proofs.P03CompactPairing
import Yau.Proofs.P03HolomorphicChartCriteria
import Yau.Proofs.P03Measure
import Yau.LeafProofs.L14

open scoped Manifold Topology ContDiff
open Set MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.LeafProofs.L14Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The original scalar CR test, realized as a continuous linear functional
on the actual compact-open continuous-function space. -/
def scalarCRTestCLM (a : M.Carrier) (i : Fin n) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ chartTarget a) : C(M.Carrier, ℂ) →L[ℂ] ℂ := by
  let K := tsupport ψ
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hc.isCompact
  let μ : Measure K := volume.comap (Subtype.val : K → ComplexVector n)
  letI : IsFiniteMeasureOnCompacts μ :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hc.isCompact.measurableSet)
  let j : C(K, M.Carrier) := ⟨fun z => chartInv a z,
    (continuousOn_extChartAt_symm (I := ComplexModel n) a).comp_continuous
      continuous_subtype_val (fun z => hs z.2)⟩
  let w : C(K, ℂ) := ⟨fun z => wirtBar ψ z (stdVec i),
    (wirtBar_contDiff ψ hψ (stdVec i)).continuous.comp continuous_subtype_val⟩
  exact compactPairingCLM μ j w

theorem scalarCRTestCLM_apply (a : M.Carrier) (i : Fin n) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ chartTarget a) (f : C(M.Carrier, ℂ)) :
    scalarCRTestCLM a i ψ hψ hc hs f =
      ∫ z, inChart a f z * wirtBar ψ z (stdVec i) ∂lebesgueC n := by
  letI : CompactSpace (tsupport ψ) := isCompact_iff_compactSpace.mp hc.isCompact
  letI : IsFiniteMeasureOnCompacts (volume.comap (Subtype.val : tsupport ψ → ComplexVector n)) :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe hc.isCompact.measurableSet)
  unfold scalarCRTestCLM
  rw [compactPairingCLM_apply]
  change (∫ z : tsupport ψ, wirtBar ψ z (stdVec i) * inChart a f z
    ∂volume.comap (Subtype.val : tsupport ψ → ComplexVector n)) = _
  rw [integral_subtype_comap hc.isCompact.measurableSet
    (fun z => wirtBar ψ z (stdVec i) * inChart a f z)]
  simp_rw [mul_comm (wirtBar ψ _ _)]
  rw [← actualMeasure_eq_volume n]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hw : wirtBar ψ z (stdVec i) = 0 := by
    by_contra hw
    exact hz (support_wirtBar_subset ψ (stdVec i) hw)
  rw [hw, mul_zero]

end Yau.NodeProofs.P03Aux
