import Yau.Proofs.F01FiniteTaylorComposition
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-! Genuine clock derivatives of all native frame evaluations determine
the clock derivative of the full spatial tensor, also in dimension zero. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

theorem spatial_tensor_clock_jet_within_of_native_frame
    (k : ℕ)
    (f : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ)
    (v : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ)
    {I : Set ℝ} {t : ℝ} (ht : t ∈ I) (hCont : ContinuousWithinAt f I t)
    (hEval : ∀ m : Fin k → RIdx n,
      HasDerivWithinAt (fun s => f s (fun i => realVec (m i)))
        (v (fun i => realVec (m i))) I t) : HasDerivWithinAt f v I t := by
  letI := continuousMultilinearMap_finiteDimensional (E := Space n) (F := ℝ) k
  let L : (ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ) →L[ℝ]
      ((Fin k → RIdx n) → ℝ) := (spatialTensorBasisEvaluation (n := n) k).toContinuousLinearMap
  have hEmb : Topology.IsEmbedding L :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr (spatialTensorBasisEvaluation_injective (n := n) k))).isEmbedding
  have hPi : HasDerivWithinAt (fun s => L (f s)) (L v) I t := by
    apply hasDerivWithinAt_pi.mpr
    intro m
    simpa only [L, LinearMap.coe_toContinuousLinearMap', spatialTensorBasisEvaluation,
      LinearMap.coe_mk, AddHom.coe_mk, Yau.LeafProofs.L12Aux.realVec_basis_apply] using hEval m
  have hSpan : ContinuousLinearMap.toSpanSingleton ℝ (L v) =
      L.comp (ContinuousLinearMap.toSpanSingleton ℝ v) := by
    apply ContinuousLinearMap.ext
    intro s
    simp
  have hComp := hPi.hasFDerivWithinAt
  rw [hSpan] at hComp
  have hTendsto : Tendsto f (𝓝[I] t) (𝓝[univ] (f t)) := by
    simpa only [nhdsWithin_univ] using hCont.tendsto
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
    (HasFDerivWithinAt.of_comp_of_isEmbedding hTendsto
      L.hasFDerivAt.hasFDerivWithinAt hEmb hComp Filter.EventuallyEq.rfl ht).hasDerivWithinAt

theorem spatial_tensor_clock_jet_of_native_frame
    (k : ℕ)
    (f : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ)
    (v : ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ)
    (t : ℝ) (hCont : ContinuousAt f t)
    (hEval : ∀ m : Fin k → RIdx n,
      HasDerivAt (fun s => f s (fun i => realVec (m i)))
        (v (fun i => realVec (m i))) t) : HasDerivAt f v t := by
  have hh := spatial_tensor_clock_jet_within_of_native_frame k f v (mem_univ t)
    hCont.continuousWithinAt (fun m => (hEval m).hasDerivWithinAt)
  simpa only [hasDerivWithinAt_univ] using hh

end Yau.NodeProofs.F01Aux
