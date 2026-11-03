import Yau.Proofs.F01SecondSpatialJetCurrying

/-! Differentiating a fixed continuous linear second-order operator
gives a fixed continuous linear map of every higher Taylor jet. The
identity uses actual derivatives on an open spatial domain. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def secondOrderSpatialJetCLM
    (B : (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) →L[ℝ] G) :
    (k : ℕ) → (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 2) => E) F) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G
  | 0 => (continuousMultilinearCurryFin0 ℝ E G).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B
  | k + 1 =>
    let L := secondOrderSpatialJetCLM B k
    let C : (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 3) => E) F) →L[ℝ]
        (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin (k + 2) => E) F) :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 3) => E) F).toContinuousLinearEquiv.toContinuousLinearMap
    let U : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) G :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) G).symm.toContinuousLinearEquiv.toContinuousLinearMap
    U.comp (((ContinuousLinearMap.compL ℝ E
      (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 2) => E) F)
      (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) G)) L).comp C)

theorem secondOrderSpatialJetCLM_native
    (B : (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F) →L[ℝ] G)
    {q : E → F} {b : E → G} {O : Set E} (hO : IsOpen O) (hq : ContDiffOn ℝ ∞ q O)
    (hRep : ∀ x ∈ O, b x = B (iteratedFDeriv ℝ 2 q x))
    (k : ℕ) {x : E} (hx : x ∈ O) :
    secondOrderSpatialJetCLM B k (iteratedFDeriv ℝ (k + 2) q x) = iteratedFDeriv ℝ k b x := by
  induction k generalizing x with
  | zero =>
    apply ContinuousMultilinearMap.ext
    intro v
    change B (iteratedFDeriv ℝ 2 q x) = b x
    exact (hRep x hx).symm
  | succ k ih =>
    let L := secondOrderSpatialJetCLM B k
    have hEq : (iteratedFDeriv ℝ k b) =ᶠ[𝓝 x]
        (fun z => L (iteratedFDeriv ℝ (k + 2) q z)) := by
      filter_upwards [hO.mem_nhds hx] with z hz using (ih hz).symm
    have hDiff : DifferentiableAt ℝ (iteratedFDeriv ℝ (k + 2) q) x :=
      (hq.contDiffAt (hO.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl (k + 2))
    have hComp : fderiv ℝ (fun z => L (iteratedFDeriv ℝ (k + 2) q z)) x =
        L.comp (fderiv ℝ (iteratedFDeriv ℝ (k + 2) q) x) :=
      (L.hasFDerivAt.comp x hDiff.hasFDerivAt).fderiv
    have hDer : fderiv ℝ (iteratedFDeriv ℝ k b) x =
        L.comp ((iteratedFDeriv ℝ (k + 3) q x).curryLeft) := by
      calc
        _ = fderiv ℝ (fun z => L (iteratedFDeriv ℝ (k + 2) q z)) x := hEq.fderiv_eq
        _ = L.comp (fderiv ℝ (iteratedFDeriv ℝ (k + 2) q) x) := hComp
        _ = _ := by rw [fderiv_iteratedFDeriv]; rfl
    have hTarget : iteratedFDeriv ℝ (k + 1) b x =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) G).symm
          (fderiv ℝ (iteratedFDeriv ℝ k b) x) := rfl
    rw [hTarget, hDer]
    rfl

end Yau.NodeProofs.F01Aux
