import Yau.Proofs.P03HilbertConstraintSets
import Yau.Proofs.P03HilbertWeightMultiplier
import Yau.Proofs.P03HilbertNormBounds
import Yau.Proofs.P03WeightMonotonicity
import Yau.Proofs.P04NestedConvex
import Yau.LeafProofs.L14Exact

open scoped Manifold Topology ContDiff
open Set MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs.L14Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Actual L14 solutions at the smooth weights have one common actual
representative satisfying the fixed equation and every regularized bound.
The source's fixed-background L² condition is supplied by its smooth compact
support in the interpolation construction. -/
theorem one_solution_all_regularized_bounds (g : Yau.SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric (M := M) E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (hE : Holomorphic (r := r) E) (Φ : M.Carrier → ℝ) (hΦ : SmoothFn Φ)
    (p : ℕ → M.Carrier → ℝ) (hp : ∀ j, SmoothFn (p j))
    (hpc : ∀ j, HasCompactSupport (p j)) (hp0 : ∀ j x, p j x ≤ 0)
    (hpm : ∀ x, Antitone (fun j => p j x))
    (f : NQForm E 1) (hf : WeaklyClosed (r := r) E f)
    (hfbase : WeightedL2 (r := r) E g.form h μ Φ f)
    (hcurv : ∀ j, WeightedNakanoNonnegative (r := r) E h (fun x => Φ x + p j x))
    (B : ℝ) (hB : 0 ≤ B)
    (hsource : ∀ j, inverseCurvatureIntegral (r := r) E g.form h μ (fun x => Φ x + p j x) f ≤
      ENNReal.ofReal B) :
    ∃ u : NQForm E 0, WeakDbar (r := r) E u f ∧
      WeightedL2 (r := r) E g.form h μ Φ u ∧
      ∀ j, weightedNormSq (r := r) E g.form h μ (fun x => Φ x + p j x) u ≤ ENNReal.ofReal B := by
  classical
  choose C hC hCbound using fun j => exists_poleMultiplier_bound (p j) (hp j) (hpc j)
  let H := WeightedTopHilbert E g μ hμ h hh Φ hΦ
  let F : WeightedOneSection E g μ hμ h hh Φ hΦ := ⟨f, hfbase⟩
  let T (j : ℕ) : H →L[ℂ] H := poleHilbertMultiplier E g μ hμ h hh Φ hΦ
    (p j) (hp j) (C j) (hC j) (hCbound j)
  let R (v : H) := (weightedTopHilbertRepresentative E g μ hμ h hh Φ hΦ v).1
  let K (j : ℕ) : Set H := regularizedHilbertConstraint E g μ hμ h hh Φ hΦ F (T j) (Real.sqrt B)
  have hnorm (j : ℕ) (v : H) : ENNReal.ofReal (‖T j v‖ ^ 2) =
      weightedNormSq (r := r) E g.form h μ (fun x => Φ x + p j x) (R v) :=
    poleHilbertMultiplier_normSq E g μ hμ h hh Φ hΦ (p j) (hp j) (C j) (hC j) (hCbound j) v
  have hmem (j : ℕ) (v : H) : v ∈ K j ↔ WeakDbar (r := r) E (R v) f ∧
      weightedNormSq (r := r) E g.form h μ (fun x => Φ x + p j x) (R v) ≤ ENNReal.ofReal B := by
    change v ∈ regularizedHilbertConstraint E g μ hμ h hh Φ hΦ F (T j) (Real.sqrt B) ↔ _
    rw [regularizedHilbertConstraint_mem_iff,
      ← ofReal_norm_sq_le_iff_norm_le_sqrt (T j v) hB, hnorm]
  have hφ (j : ℕ) : SmoothFn (fun x => Φ x + p j x) := fun a => (hΦ a).add (hp j a)
  have hle (j : ℕ) (x : M.Carrier) : Φ x + p j x ≤ Φ x := by have hh := hp0 j x; linarith
  have hnonempty (j : ℕ) : (K j).Nonempty := by
    obtain ⟨u, hu, hw, hub⟩ := weightedDbarEstimate E g μ h (fun x => Φ x + p j x)
      hμ hE hh (hφ j) (hcurv j) f hf ((hsource j).trans_lt ENNReal.ofReal_lt_top)
    let U : WeightedTopSection E g μ hμ h hh Φ hΦ :=
      ⟨u, weightedTopL2_mono_weight E g.form h μ u (hle j) hu⟩
    let v : H := realizeWeightedTopSection E g μ hμ h hh Φ hΦ U
    have hv : v ∈ fixedSourceSolutionSet E g μ hμ h hh Φ hΦ F :=
      (weightedMaximalDbarHilbertGraph_realize_iff E g μ hμ h hh Φ hΦ U F).mpr hw
    have hweak := (fixedSourceSolutionSet_mem_iff E g μ hμ h hh Φ hΦ F v).mp hv
    have hae : ∀ᵐ x ∂μ, R v x = u x :=
      (realizeWeightedTopSection_eq_iff_ae E g μ hμ h hh Φ hΦ
        (weightedTopHilbertRepresentative E g μ hμ h hh Φ hΦ v) U).mp
        (weightedTopHilbertRepresentative_realize E g μ hμ h hh Φ hΦ v)
    refine ⟨v, (hmem j v).mpr ⟨hweak, ?_⟩⟩
    rw [weightedNormSq_congr_ae E g.form h μ (fun x => Φ x + p j x) (R v) u hae]
    exact hub.trans (hsource j)
  have hclosed (j : ℕ) : IsClosed (K j) :=
    regularizedHilbertConstraint_isClosed E g μ hμ h hh Φ hΦ F (T j) (Real.sqrt B)
  have hconvex (j : ℕ) : Convex ℝ (K j) :=
    regularizedHilbertConstraint_convex E g μ hμ h hh Φ hΦ F (T j) (Real.sqrt B)
  have hnested : Antitone K := by
    intro i j hij v hv
    obtain ⟨hw, hb⟩ := (hmem j v).mp hv
    apply (hmem i v).mpr
    exact ⟨hw, (weightedTopNormSq_antitone_weight E g.form h μ (R v)
      (fun x => add_le_add (le_refl (Φ x)) (hpm x hij))).trans hb⟩
  have hbounded (j : ℕ) (v : H) (hv : v ∈ K j) : ‖v‖ ≤ Real.sqrt B := by
    have hb := (hmem j v).mp hv |>.2
    have hbase := (weightedTopNormSq_antitone_weight E g.form h μ (R v) (hle j)).trans hb
    rw [weightedTopHilbertRepresentative_normSq E g μ hμ h hh Φ hΦ v] at hbase
    exact (ofReal_norm_sq_le_iff_norm_le_sqrt v hB).mp hbase
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  obtain ⟨v, hv⟩ := Yau.Proofs.P04Aux.exists_mem_all_nested_closed_convex K hnonempty hclosed hconvex
    hnested (Real.sqrt B) hbounded
  exact ⟨R v, (hmem 0 v).mp (hv 0) |>.1,
    (weightedTopHilbertRepresentative E g μ hμ h hh Φ hΦ v).2,
    fun j => (hmem j v).mp (hv j) |>.2⟩

end Yau.NodeProofs.P03Aux
