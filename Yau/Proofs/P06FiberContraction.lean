import Yau.Proofs.P06Geometry

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem scalarForm_normSq (h : HermitianField M) (f : M.Carrier → ℝ) (x : M.Carrier) :
    formNormSq h (G04Aux.scalarForm f) x = (f x) ^ 2 := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  simp [formNormSq, formInner, G04Aux.scalarForm_components, inChart, hx, sq]

theorem scalarForm_add (f q : M.Carrier → ℝ) :
    G04Aux.scalarForm (f + q) = G04Aux.scalarForm f + G04Aux.scalarForm q := by
  funext x
  ext v
  rfl

theorem scalarForm_smul (c : ℝ) (f : M.Carrier → ℝ) :
    G04Aux.scalarForm (c • f) = c • G04Aux.scalarForm f := by
  funext x
  ext v
  rfl

def fiberContraction (h : HermitianField M) (B : RealForm M k) :
    RealForm M k →ₗ[ℝ] RealForm M 0 where
  toFun A := G04Aux.scalarForm (formInner h A B)
  map_add' A D := by rw [formInner_add_left, scalarForm_add]
  map_smul' c A := by
    change G04Aux.scalarForm (formInner h (c • A) B) = c • G04Aux.scalarForm (formInner h A B)
    rw [formInner_smul_left, scalarForm_smul]

theorem l2RealForm_fiberContraction (g : SmoothMetric M) (μ : Measure M.Carrier)
    (B : RealForm M k) (hB : SmoothRealForm B) (C : ℝ)
    (hbound : ∀ x, formNormSq g.form B x ≤ C ^ 2)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    L2RealForm g.form μ (fiberContraction g.form B A) := by
  have hm := formInner_aestronglyMeasurable_of_coefficients g μ A B hA.1
    (smoothRealForm_coefficient_aestronglyMeasurable μ B hB)
  have hc : ∀ x (I : Fin 0 → RIdx n), AEStronglyMeasurable
      (fun y => fiberContraction g.form B A y (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
    intro x I
    exact hm.mono_measure Measure.restrict_le_self
  have hb : ∀ x, formNormSq g.form (fiberContraction g.form B A) x ≤
      C ^ 2 * formNormSq g.form A x := by
    intro x
    rw [show fiberContraction g.form B A = G04Aux.scalarForm (formInner g.form A B) from rfl,
      scalarForm_normSq]
    exact (formInner_sq_le g.form A B x).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound x) (formNormSq_nonneg g.form A x))
  have hn : Integrable (formNormSq g.form (fiberContraction g.form B A)) μ := by
    apply ((formNormSq_integrable g μ A hA).const_mul (C ^ 2)).mono_nonneg
      (formInner_aestronglyMeasurable_of_coefficients g μ _ _ hc hc)
      (Filter.Eventually.of_forall (fun x => formNormSq_nonneg g.form _ x))
    exact Filter.Eventually.of_forall hb
  refine ⟨hc, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun x => formNormSq_nonneg g.form _ x))).mp hn.2

def fiberContractionL2Linear (g : SmoothMetric M) (μ : Measure M.Carrier)
    (B : RealForm M k) (hB : SmoothRealForm B) (C : ℝ)
    (hbound : ∀ x, formNormSq g.form B x ≤ C ^ 2) :
    L2FormSpace g μ k →ₗ[ℝ] L2FormSpace g μ 0 where
  toFun u := L2FormSpace.ofSection (fiberContraction g.form B u.toSection)
    (l2RealForm_fiberContraction g μ B hB C hbound u.toSection u.toSection_l2)
  map_add' u v := by
    apply L2FormSpace.toSection_injective g μ 0
    change fiberContraction g.form B (u + v).toSection =
      fiberContraction g.form B u.toSection + fiberContraction g.form B v.toSection
    rw [L2FormSpace.toSection_add, map_add]
  map_smul' c u := by
    apply L2FormSpace.toSection_injective g μ 0
    change fiberContraction g.form B (c • u).toSection = c • fiberContraction g.form B u.toSection
    rw [L2FormSpace.toSection_smul, map_smul]

theorem fiberContractionL2Linear_toSection (g : SmoothMetric M) (μ : Measure M.Carrier)
    (B : RealForm M k) (hB : SmoothRealForm B) (C : ℝ)
    (hbound : ∀ x, formNormSq g.form B x ≤ C ^ 2) (u : L2FormSpace g μ k) :
    (fiberContractionL2Linear g μ B hB C hbound u).toSection =
      fiberContraction g.form B u.toSection := rfl

theorem fiberContractionL2Linear_norm_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (B : RealForm M k) (hB : SmoothRealForm B) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, formNormSq g.form B x ≤ C ^ 2) (u : L2FormSpace g μ k) :
    ‖fiberContractionL2Linear g μ B hB C hbound u‖ ≤ C * ‖u‖ := by
  have hA := u.toSection_l2
  have hout := l2RealForm_fiberContraction g μ B hB C hbound u.toSection hA
  have hi := integral_mono (formNormSq_integrable g μ _ hout)
    ((formNormSq_integrable g μ u.toSection hA).const_mul (C ^ 2)) (fun x => by
      change formNormSq g.form (G04Aux.scalarForm (formInner g.form u.toSection B)) x ≤ _
      rw [scalarForm_normSq]
      exact (formInner_sq_le g.form u.toSection B x).trans
        (by simpa only [mul_comm] using
          (mul_le_mul_of_nonneg_left (hbound x) (formNormSq_nonneg g.form u.toSection x))))
  rw [integral_const_mul] at hi
  have hs : ‖fiberContractionL2Linear g μ B hB C hbound u‖ ^ 2 ≤ C ^ 2 * ‖u‖ ^ 2 := by
    simpa only [l2FormSpace_norm_sq, fiberContractionL2Linear_toSection] using hi
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg u))).mp
  nlinarith

def fiberContractionHilbert (g : SmoothMetric M) (μ : Measure M.Carrier)
    (B : RealForm M k) (hB : SmoothRealForm B) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, formNormSq g.form B x ≤ C ^ 2) :
    L2FormHilbert g μ k →L[ℝ] L2FormHilbert g μ 0 :=
  ((fiberContractionL2Linear g μ B hB C hbound).mkContinuous C
    (fiberContractionL2Linear_norm_le g μ B hB C hC hbound)).completion

theorem fiberContractionHilbert_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (B : RealForm M k) (hB : SmoothRealForm B) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, formNormSq g.form B x ≤ C ^ 2) (u : L2FormSpace g μ k) :
    fiberContractionHilbert g μ B hB C hC hbound (realizeL2Form g μ u) =
      realizeL2Form g μ (fiberContractionL2Linear g μ B hB C hbound u) :=
  ContinuousLinearMap.completion_apply_coe _ u

end Yau.NodeProofs.P06Aux
