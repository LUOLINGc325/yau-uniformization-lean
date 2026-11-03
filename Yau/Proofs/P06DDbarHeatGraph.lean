import Yau.Proofs.P06DDbarHeatEnergy

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}

def ddForm (A : RealForm M 0) : RealForm M 2 := ddRealForm (WeakCurrent.scalarValue A)

theorem ddForm_smooth (A : RealForm M 0) (hA : SmoothRealForm A) : SmoothRealForm (ddForm A) :=
  dd_smooth _ (WeakCurrent.scalarValue_smooth A hA)

theorem ddForm_compact (A : RealForm M 0) (hA : SmoothRealForm A)
    (hcA : CompactlySupportedRealForm A) : CompactlySupportedRealForm (ddForm A) :=
  dd_compact _ (WeakCurrent.scalarValue_smooth A hA) (WeakCurrent.scalarValue_compact A hcA)

theorem ddForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 0)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) : L2RealForm g.form μ (ddForm A) :=
  smooth_compactlySupported_l2RealForm g μ hμ _ (ddForm_smooth A hA) (ddForm_compact A hA hcA)

theorem ddForm_add (A B : RealForm M 0) (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    ddForm (A+B) = ddForm A + ddForm B :=
  dd_add _ _ (WeakCurrent.scalarValue_smooth A hA) (WeakCurrent.scalarValue_smooth B hB)

theorem ddForm_smul (c : ℝ) (A : RealForm M 0) (hA : SmoothRealForm A) :
    ddForm (c • A) = c • ddForm A :=
  dd_smul c _ (WeakCurrent.scalarValue_smooth A hA)

theorem ddForm_sub (A B : RealForm M 0) (hA : SmoothRealForm A) (hB : SmoothRealForm B) :
    ddForm (A-B) = ddForm A - ddForm B :=
  dd_sub _ _ (WeakCurrent.scalarValue_smooth A hA) (WeakCurrent.scalarValue_smooth B hB)

def adjointForm (g : HermitianField M) (B : RealForm M 2) : RealForm M 0 :=
  scalarForm (WeakCurrent.ddAdjointScalar g B)

theorem adjointForm_smooth (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2) (hB : SmoothRealForm B) :
    SmoothRealForm (adjointForm g.form B) :=
  scalarForm_smooth _ (WeakCurrent.ddAdjointScalar_smooth g μ hμ B hB)

theorem adjointForm_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    CompactlySupportedRealForm (adjointForm g.form B) :=
  scalarForm_compact _ (WeakCurrent.ddAdjointScalar_compact g μ hμ B hB hcB)

theorem adjointForm_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    L2RealForm g.form μ (adjointForm g.form B) :=
  smooth_compactlySupported_l2RealForm g μ hμ _ (adjointForm_smooth g μ hμ B hB)
    (adjointForm_compact g μ hμ B hB hcB)

theorem integral_ddForm_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 0) (hA : SmoothRealForm A)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ x, formInner g.form (ddForm A) B x ∂μ) =
      ∫ x, formInner g.form A (adjointForm g.form B) x ∂μ := by
  rw [ddForm, WeakCurrent.integral_dd_eq_adjoint g μ hμ _ (WeakCurrent.scalarValue_smooth A hA)
    B hB hcB, ← scalarForm_scalarValue A]
  simp only [adjointForm, WeakCurrent.formInner_scalar]
  rfl

def ddCorePair (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 0)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    L2FormHilbert g μ 0 × L2FormHilbert g μ 2 :=
  (realizeActualForm g μ A (smooth_compactlySupported_l2RealForm g μ hμ A hA hcA),
    realizeActualForm g μ (ddForm A) (ddForm_l2 g μ hμ A hA hcA))

theorem ddCorePair_add (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 0)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    ddCorePair g μ hμ (A+B) (smoothRealForm_add A B hA hB)
      (compactlySupportedRealForm_add A B hcA hcB) =
      ddCorePair g μ hμ A hA hcA + ddCorePair g μ hμ B hB hcB := by
  apply Prod.ext
  · exact realizeActualForm_add g μ A B _ _
  · exact (realizeActualForm_congr g μ _ _ _ _ (ddForm_add A B hA hB)).trans
      (realizeActualForm_add g μ _ _ _ _)

theorem ddCorePair_smul (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (c : ℝ) (A : RealForm M 0)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    ddCorePair g μ hμ (c • A) (smoothRealForm_smul c A hA)
      (compactlySupportedRealForm_smul c A hcA) = c • ddCorePair g μ hμ A hA hcA := by
  apply Prod.ext
  · exact realizeActualForm_smul g μ c A _
  · exact (realizeActualForm_congr g μ _ _ _ _ (ddForm_smul c A hA)).trans
      (realizeActualForm_smul g μ c _ _)

/-- Closure of the actual compact expression -(1/2)dJd. -/
def ddCoreGraph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    Submodule ℝ (L2FormHilbert g μ 0 × L2FormHilbert g μ 2) where
  carrier := {p | ∃ (A : RealForm M 0) (hA : SmoothRealForm A)
    (hcA : CompactlySupportedRealForm A), p = ddCorePair g μ hμ A hA hcA}
  zero_mem' := by
    have hs : SmoothRealForm (0 : RealForm M 0) := smoothRealForm_zero
    have hc : CompactlySupportedRealForm (0 : RealForm M 0) := by
      simpa [CompactlySupportedRealForm] using (isCompact_empty : IsCompact (∅ : Set M.Carrier))
    refine ⟨0, hs, hc, ?_⟩
    simpa only [zero_smul] using (ddCorePair_smul g μ hμ 0 0 hs hc).symm
  add_mem' := by
    rintro p q ⟨A,hA,hcA,rfl⟩ ⟨B,hB,hcB,rfl⟩
    exact ⟨A+B,smoothRealForm_add A B hA hB,compactlySupportedRealForm_add A B hcA hcB,
      (ddCorePair_add g μ hμ A B hA hcA hB hcB).symm⟩
  smul_mem' := by
    rintro c p ⟨A,hA,hcA,rfl⟩
    exact ⟨c • A,smoothRealForm_smul c A hA,compactlySupportedRealForm_smul c A hcA,
      (ddCorePair_smul g μ hμ c A hA hcA).symm⟩

def ddGraph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) := (ddCoreGraph g μ hμ).topologicalClosure

theorem ddGraph_weak_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : L2FormHilbert g μ 0} {v : L2FormHilbert g μ 2}
    (huv : (u,v) ∈ ddGraph g μ hμ) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    inner ℝ v (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) =
      inner ℝ u (realizeActualForm g μ (adjointForm g.form B) (adjointForm_l2 g μ hμ B hB hcB)) := by
  let b := realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)
  let q := realizeActualForm g μ (adjointForm g.form B) (adjointForm_l2 g μ hμ B hB hcB)
  let L : (L2FormHilbert g μ 0 × L2FormHilbert g μ 2) →L[ℝ] ℝ :=
    (innerSL ℝ b).comp (ContinuousLinearMap.snd ℝ _ _) -
      (innerSL ℝ q).comp (ContinuousLinearMap.fst ℝ _ _)
  have hs : ddCoreGraph g μ hμ ≤ L.ker := by
    rintro p ⟨A,hA,hcA,rfl⟩
    change inner ℝ b (realizeActualForm g μ (ddForm A) _) -
      inner ℝ q (realizeActualForm g μ A _) = 0
    rw [real_inner_comm (realizeActualForm g μ (ddForm A) _) b,
      real_inner_comm (realizeActualForm g μ A _) q]
    dsimp only [b,q]
    rw [realizeActualForm_inner, realizeActualForm_inner]
    exact sub_eq_zero.mpr (integral_ddForm_adjoint g μ hμ A hA B hB hcB)
  have he := ((ddCoreGraph g μ hμ).topologicalClosure_minimal hs L.isClosed_ker) huv
  change inner ℝ b v - inner ℝ q u = 0 at he
  simpa only [real_inner_comm] using sub_eq_zero.mp he

theorem ddGraph_no_vertical (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (p : L2FormHilbert g μ 0 × L2FormHilbert g μ 2)
    (hp : p ∈ ddGraph g μ hμ) (h0 : p.1 = 0) : p.2 = 0 := by
  apply hilbert_zero_of_compact_form_pairings g μ hμ
  intro B hB hcB
  rw [ddGraph_weak_pairing g μ hμ hp B hB hcB, h0, inner_zero_left]

def closedDDbar (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : L2FormHilbert g μ 0 →ₗ.[ℝ] L2FormHilbert g μ 2 :=
  (ddGraph g μ hμ).toLinearPMap

theorem closedDDbar_graph (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : (closedDDbar g μ hμ).graph = ddGraph g μ hμ :=
  Submodule.toLinearPMap_graph_eq _ (ddGraph_no_vertical g μ hμ)

theorem closedDDbar_isClosed (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) : (closedDDbar g μ hμ).IsClosed := by
  rw [LinearPMap.IsClosed, closedDDbar_graph]
  exact (ddCoreGraph g μ hμ).isClosed_topologicalClosure

theorem ddGraph_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 0)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    ddCorePair g μ hμ A hA hcA ∈ (closedDDbar g μ hμ).graph := by
  rw [closedDDbar_graph]
  exact (ddCoreGraph g μ hμ).le_topologicalClosure ⟨A,hA,hcA,rfl⟩

theorem ddGraph_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {u : L2FormHilbert g μ 0} {v : L2FormHilbert g μ 2}
    (huv : (u,v) ∈ (closedDDbar g μ hμ).graph) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    inner ℝ v (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)) =
      inner ℝ u (realizeActualForm g μ (adjointForm g.form B) (adjointForm_l2 g μ hμ B hB hcB)) := by
  rw [closedDDbar_graph] at huv
  exact ddGraph_weak_pairing g μ hμ huv B hB hcB

theorem closedDDbar_dense (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) :
    Dense ((closedDDbar g μ hμ).domain : Set (L2FormHilbert g μ 0)) := by
  apply (hodgeCoreRealizedGraph_domain_dense g μ hμ 0).mono
  rintro u ⟨p,⟨A,W,hc,rfl⟩,rfl⟩
  rw [← LinearPMap.graph_map_fst_eq_domain]
  exact ⟨ddCorePair g μ hμ A hc.1 hc.2.1,ddGraph_core g μ hμ A hc.1 hc.2.1,rfl⟩

end Yau.NodeProofs.P06Aux.DDbarHeat
