import Yau.Proofs.P06HodgeEnergyCore
import Yau.Proofs.P06HodgeEuler
import Yau.Proofs.P06DifferentialComplex

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

def exteriorCorePair (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    L2FormHilbert g μ k × L2FormHilbert g μ (k+1) :=
  (realizeActualForm g μ A (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA),
    realizeActualForm g μ (exteriorRealForm A) (exteriorRealForm_l2 g μ hμ A hA hcA))

theorem exteriorCorePair_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    exteriorCorePair g μ hμ (A+B) (smoothRealForm_add A B hA hB)
      (compactlySupportedRealForm_add A B hcA hcB) =
      exteriorCorePair g μ hμ A hA hcA + exteriorCorePair g μ hμ B hB hcB := by
  apply Prod.ext
  · exact realizeActualForm_add g μ A B _ _
  · change realizeActualForm g μ (exteriorRealForm (A+B)) _ = _
    exact (realizeActualForm_congr g μ _ _ _ _ (exteriorRealForm_add A B hA hB)).trans
      (realizeActualForm_add g μ _ _ _ _)

theorem exteriorCorePair_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (c : ℝ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    exteriorCorePair g μ hμ (c • A) (smoothRealForm_smul c A hA)
      (compactlySupportedRealForm_smul c A hcA) = c • exteriorCorePair g μ hμ A hA hcA := by
  apply Prod.ext
  · exact realizeActualForm_smul g μ c A _
  · change realizeActualForm g μ (exteriorRealForm (c • A)) _ = _
    exact (realizeActualForm_congr g μ _ _ _ _ (exteriorRealForm_smul c A hA)).trans
      (realizeActualForm_smul g μ c _ _)

/-- The actual compact smooth exterior graph. -/
def exteriorCoreGraph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    Submodule ℝ (L2FormHilbert g μ k × L2FormHilbert g μ (k+1)) where
  carrier := {p | ∃ (A : RealForm M k) (hA : SmoothRealForm A)
    (hcA : CompactlySupportedRealForm A), p = exteriorCorePair g μ hμ A hA hcA}
  zero_mem' := by
    have hs : SmoothRealForm (0 : RealForm M k) := smoothRealForm_zero
    have hc : CompactlySupportedRealForm (0 : RealForm M k) := by
      simpa [CompactlySupportedRealForm] using (isCompact_empty : IsCompact (∅ : Set M.Carrier))
    refine ⟨0, hs, hc, ?_⟩
    simpa only [zero_smul] using (exteriorCorePair_smul g μ hμ 0 0 hs hc).symm
  add_mem' := by
    rintro p q ⟨A, hA, hcA, rfl⟩ ⟨B, hB, hcB, rfl⟩
    exact ⟨A+B, smoothRealForm_add A B hA hB,
      compactlySupportedRealForm_add A B hcA hcB,
      (exteriorCorePair_add g μ hμ A B hA hcA hB hcB).symm⟩
  smul_mem' := by
    rintro c p ⟨A, hA, hcA, rfl⟩
    exact ⟨c • A, smoothRealForm_smul c A hA, compactlySupportedRealForm_smul c A hcA,
      (exteriorCorePair_smul g μ hμ c A hA hcA).symm⟩

def exteriorGraph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :=
  (exteriorCoreGraph g μ hμ k).topologicalClosure

theorem exteriorGraph_weak_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : L2FormHilbert g μ k}
    {v : L2FormHilbert g μ (k+1)} (huv : (u,v) ∈ exteriorGraph g μ hμ k)
    (B : RealForm M (k+1)) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    inner ℝ v (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) =
      inner ℝ u (realizeActualForm g μ (codifferentialRealForm g.form B)
        (codifferentialRealForm_l2 g μ hμ B hB hcB)) := by
  let b := realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)
  let c := realizeActualForm g μ (codifferentialRealForm g.form B)
    (codifferentialRealForm_l2 g μ hμ B hB hcB)
  let L : (L2FormHilbert g μ k × L2FormHilbert g μ (k+1)) →L[ℝ] ℝ :=
    (innerSL ℝ b).comp (ContinuousLinearMap.snd ℝ _ _) -
      (innerSL ℝ c).comp (ContinuousLinearMap.fst ℝ _ _)
  have hs : exteriorCoreGraph g μ hμ k ≤ L.ker := by
    rintro p ⟨A, hA, hcA, rfl⟩
    change inner ℝ b (realizeActualForm g μ (exteriorRealForm A) _) -
      inner ℝ c (realizeActualForm g μ A _) = 0
    rw [real_inner_comm (realizeActualForm g μ (exteriorRealForm A) _) b,
      real_inner_comm (realizeActualForm g μ A _) c]
    dsimp only [b,c]
    rw [realizeActualForm_inner, realizeActualForm_inner]
    exact sub_eq_zero.mpr (integral_exterior_codifferential g μ hμ A B hA hB hcA)
  have he := ((exteriorCoreGraph g μ hμ k).topologicalClosure_minimal hs L.isClosed_ker) huv
  change inner ℝ b v - inner ℝ c u = 0 at he
  simpa only [real_inner_comm] using sub_eq_zero.mp he

theorem exteriorGraph_no_vertical (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ)
    (p : L2FormHilbert g μ k × L2FormHilbert g μ (k+1))
    (hp : p ∈ exteriorGraph g μ hμ k) (h0 : p.1 = 0) : p.2 = 0 := by
  apply hilbert_zero_of_compact_form_pairings g μ hμ
  intro B hB hcB
  rw [exteriorGraph_weak_pairing g μ hμ hp B hB hcB, h0, inner_zero_left]

/-- The closed operator is constructed from the verified single-valued closure. -/
def closedExterior (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    L2FormHilbert g μ k →ₗ.[ℝ] L2FormHilbert g μ (k+1) :=
  (exteriorGraph g μ hμ k).toLinearPMap

theorem closedExterior_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    (closedExterior g μ hμ k).graph = exteriorGraph g μ hμ k :=
  Submodule.toLinearPMap_graph_eq _ (exteriorGraph_no_vertical g μ hμ)

theorem closedExterior_isClosed (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) : (closedExterior g μ hμ k).IsClosed := by
  rw [LinearPMap.IsClosed, closedExterior_graph]
  exact (exteriorCoreGraph g μ hμ k).isClosed_topologicalClosure

theorem exteriorGraph_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    exteriorCorePair g μ hμ A hA hcA ∈ (closedExterior g μ hμ k).graph := by
  rw [closedExterior_graph]
  exact (exteriorCoreGraph g μ hμ k).le_topologicalClosure ⟨A,hA,hcA,rfl⟩

theorem exteriorGraph_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : L2FormHilbert g μ k}
    {v : L2FormHilbert g μ (k+1)} (huv : (u,v) ∈ (closedExterior g μ hμ k).graph)
    (B : RealForm M (k+1)) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    inner ℝ v (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) =
      inner ℝ u (realizeActualForm g μ (codifferentialRealForm g.form B)
        (codifferentialRealForm_l2 g μ hμ B hB hcB)) := by
  rw [closedExterior_graph] at huv
  exact exteriorGraph_weak_pairing g μ hμ huv B hB hcB

theorem closedExterior_dense (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (k : ℕ) :
    Dense ((closedExterior g μ hμ k).domain : Set (L2FormHilbert g μ k)) := by
  apply (hodgeCoreRealizedGraph_domain_dense g μ hμ k).mono
  rintro u ⟨p, ⟨A,W,hc,rfl⟩, rfl⟩
  rw [← LinearPMap.graph_map_fst_eq_domain]
  exact ⟨exteriorCorePair g μ hμ A hc.1 hc.2.1,
    exteriorGraph_core g μ hμ A hc.1 hc.2.1, rfl⟩

end Yau.NodeProofs.P06Aux.ExteriorHeat
