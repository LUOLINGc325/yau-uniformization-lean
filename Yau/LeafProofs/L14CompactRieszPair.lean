import Yau.LeafProofs.L14CompactSource
import Yau.LeafProofs.L14RieszRange
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar
variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem smoothForm_const_smul {q : ℕ} (c : ℂ) (u : NQForm E q)
    (hu : SmoothForm (r := r) E u) : SmoothForm (r := r) E (c • u) := by
  intro a I α
  simpa only [coefficients_smul, smul_eq_mul] using (hu a I α).const_smul c

theorem compact_formSupport_zero (q : ℕ) :
    IsCompact (closure {x | (0 : NQForm E q) x ≠ (0 : NQForm E q) x}) := by simp

theorem compact_formSupport_add {q : ℕ} (u v : NQForm E q)
    (hu : IsCompact (closure {x | u x ≠ (0 : NQForm E q) x}))
    (hv : IsCompact (closure {x | v x ≠ (0 : NQForm E q) x})) :
    IsCompact (closure {x | (u+v) x ≠ (0 : NQForm E q) x}) := by
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
    compact_formSupport_sum E ![u,v] (fun i => by fin_cases i; exact hu; exact hv)

theorem compact_formSupport_smul {q : ℕ} (c : ℂ) (u : NQForm E q)
    (hu : IsCompact (closure {x | u x ≠ (0 : NQForm E q) x})) :
    IsCompact (closure {x | (c • u) x ≠ (0 : NQForm E q) x}) := by
  apply hu.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx hzero
  apply hx
  apply Subtype.ext
  rw [nqForm_smul_apply, congrArg Subtype.val hzero, nqForm_zero_apply, smul_zero]

theorem smoothDbarRepresents_add {q : ℕ} (u v : NQForm E q)
    (D F : NQForm E (q+1)) (hu : SmoothForm (r := r) E u) (hv : SmoothForm (r := r) E v)
    (hD : SmoothDbarRepresents (r := r) E u D) (hF : SmoothDbarRepresents (r := r) E v F) :
    SmoothDbarRepresents (r := r) E (u+v) (D+F) := by
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
    smoothDbarRepresents_sum E ![u,v] ![D,F]
      (fun i => by fin_cases i; exact hu; exact hv)
      (fun i => by fin_cases i; exact hD; exact hF)

theorem wirtBar_const_mul_local (c : ℂ) (F : ComplexVector n → ℂ)
    (z v : ComplexVector n) (hF : DifferentiableAt ℝ F z) :
    wirtBar (fun w => c * F w) z v = c * wirtBar F z v := by
  unfold wirtBar
  rw [fderiv_const_mul hF]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem smoothDbarRepresents_smul {q : ℕ} (c : ℂ) (u : NQForm E q)
    (D : NQForm E (q+1)) (hu : SmoothForm (r := r) E u)
    (hD : SmoothDbarRepresents (r := r) E u D) :
    SmoothDbarRepresents (r := r) E (c • u) (c • D) := by
  intro a z hz I α
  rw [coefficients_smul, hD a z hz I α]
  unfold dbarCoefficients
  simp_rw [coefficients_smul]
  have hw (k : Fin (q+1)) :
      wirtBar (fun w => c * coefficients (r := r) E u a w (fun l => I (k.succAbove l)) α) z (stdVec (I k)) =
      c * wirtBar (fun w => coefficients (r := r) E u a w (fun l => I (k.succAbove l)) α) z (stdVec (I k)) :=
    wirtBar_const_mul_local c _ z _ (((hu a _ α).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp))
  simp_rw [hw, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

/-- Actual weighted sections in degrees one, zero, and two. -/
abbrev CompactJointTriple := WeightedOneSection E g μ hμ h hh φ hφ ×
  (WeightedTopSection E g μ hμ h hh φ hφ × WeightedTwoSection E g μ hμ h hh φ hφ)

/-- Compact smooth test forms satisfying both actual operator graph relations. -/
def IsCompactJointTriple (t : CompactJointTriple E g μ hμ h hh φ hφ) : Prop :=
  SmoothForm (r := r) E t.1.1 ∧ IsCompact (closure {x | t.1.1 x ≠ (0 : NQForm E 1) x}) ∧
  SmoothForm (r := r) E t.2.1.1 ∧ IsCompact (closure {x | t.2.1.1 x ≠ (0 : NQForm E 0) x}) ∧
  SmoothForm (r := r) E t.2.2.1 ∧ IsCompact (closure {x | t.2.2.1 x ≠ (0 : NQForm E 2) x}) ∧
  SmoothDbarRepresents (r := r) E t.1.1 t.2.2.1 ∧
  (realizeWeightedOneSection E g μ hμ h hh φ hφ t.1,
    realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph

/-- Complex linear space of the concrete compact graph triples. -/
def compactJointTestSpace : Submodule ℂ (CompactJointTriple E g μ hμ h hh φ hφ) where
  carrier := {t | IsCompactJointTriple E g μ hμ h hh φ hφ t}
  zero_mem' := by
    refine ⟨smoothForm_zero E 1, compact_formSupport_zero E 1,
      smoothForm_zero E 0, compact_formSupport_zero E 0,
      smoothForm_zero E 2, compact_formSupport_zero E 2, ?_, ?_⟩
    · change SmoothDbarRepresents (r := r) E (0 : NQForm E 1) (0 : NQForm E 2)
      intro a z hz I α
      simp only [dbarCoefficients, coefficients_zero, wirtBar]
      simp
    · change ((0 : WeightedOneHilbert E g μ hμ h hh φ hφ),
        (0 : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈ _
      exact Submodule.zero_mem _
  add_mem' := by
    intro t v ht hv
    refine ⟨smoothForm_add E _ _ ht.1 hv.1, compact_formSupport_add E _ _ ht.2.1 hv.2.1,
      smoothForm_add E _ _ ht.2.2.1 hv.2.2.1, compact_formSupport_add E _ _ ht.2.2.2.1 hv.2.2.2.1,
      smoothForm_add E _ _ ht.2.2.2.2.1 hv.2.2.2.2.1,
      compact_formSupport_add E _ _ ht.2.2.2.2.2.1 hv.2.2.2.2.2.1,
      smoothDbarRepresents_add E _ _ _ _ ht.1 hv.1 ht.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1, ?_⟩
    change ((↑(t.1 + v.1) : WeightedOneHilbert E g μ hμ h hh φ hφ),
      (↑(t.2.1 + v.2.1) : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈ _
    simpa only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, realizeWeightedOneSection, realizeWeightedTopSection,
      UniformSpace.Completion.coe_add] using
      Submodule.add_mem _ ht.2.2.2.2.2.2.2 hv.2.2.2.2.2.2.2
  smul_mem' := by
    intro c t ht
    refine ⟨smoothForm_const_smul E c _ ht.1, compact_formSupport_smul E c _ ht.2.1,
      smoothForm_const_smul E c _ ht.2.2.1, compact_formSupport_smul E c _ ht.2.2.2.1,
      smoothForm_const_smul E c _ ht.2.2.2.2.1,
      compact_formSupport_smul E c _ ht.2.2.2.2.2.1,
      smoothDbarRepresents_smul E c _ _ ht.1 ht.2.2.2.2.2.2.1, ?_⟩
    change ((↑(c • t.1) : WeightedOneHilbert E g μ hμ h hh φ hφ),
      (↑(c • t.2.1) : WeightedTopHilbert E g μ hμ h hh φ hφ)) ∈ _
    simpa only [Prod.smul_mk, realizeWeightedOneSection, realizeWeightedTopSection,
      UniformSpace.Completion.coe_smul] using
      Submodule.smul_mem _ c ht.2.2.2.2.2.2.2

abbrev CompactJointHilbert := WithLp 2
  (WeightedTopHilbert E g μ hμ h hh φ hφ × WeightedTwoHilbert E g μ hμ h hh φ hφ)

/-- The two graph outputs, with their Hilbert direct sum norm. -/
def compactJointLinearMap : compactJointTestSpace E g μ hμ h hh φ hφ →ₗ[ℂ]
    CompactJointHilbert E g μ hμ h hh φ hφ where
  toFun t := WithLp.toLp 2 (realizeWeightedTopSection E g μ hμ h hh φ hφ t.1.2.1,
    realizeWeightedTwoSection E g μ hμ h hh φ hφ t.1.2.2)
  map_add' t v := by
    apply WithLp.ofLp_injective 2
    change ((↑(t.1.2.1 + v.1.2.1) : WeightedTopHilbert E g μ hμ h hh φ hφ),
      (↑(t.1.2.2 + v.1.2.2) : WeightedTwoHilbert E g μ hμ h hh φ hφ)) =
      ((↑t.1.2.1 : WeightedTopHilbert E g μ hμ h hh φ hφ),
        (↑t.1.2.2 : WeightedTwoHilbert E g μ hμ h hh φ hφ)) +
      ((↑v.1.2.1 : WeightedTopHilbert E g μ hμ h hh φ hφ),
        (↑v.1.2.2 : WeightedTwoHilbert E g μ hμ h hh φ hφ))
    simp only [UniformSpace.Completion.coe_add, Prod.mk_add_mk]
  map_smul' c t := by
    apply WithLp.ofLp_injective 2
    change ((↑(c • t.1.2.1) : WeightedTopHilbert E g μ hμ h hh φ hφ),
      (↑(c • t.1.2.2) : WeightedTwoHilbert E g μ hμ h hh φ hφ)) =
      c • ((↑t.1.2.1 : WeightedTopHilbert E g μ hμ h hh φ hφ),
        (↑t.1.2.2 : WeightedTwoHilbert E g μ hμ h hh φ hφ))
    simp only [UniformSpace.Completion.coe_smul, Prod.smul_mk]

variable (hE : Holomorphic (r := r) E)

/-- Pair the original locally square integrable source against its compact test form. -/
def compactJointSource (f : NQForm E 1) (hf : LocallyL2 (r := r) E f) :
    compactJointTestSpace E g μ hμ h hh φ hφ →ₗ[ℂ] ℂ where
  toFun t := weightedOneInner E g.form μ h φ f t.1.1.1
  map_add' t v := by
    change weightedOneInner E g.form μ h φ f (t.1.1.1 + v.1.1.1) = _
    unfold weightedOneInner
    have hi (t : compactJointTestSpace E g μ hμ h hh φ hφ) := locallyL2_weightedOnePairing_compact_integrable E g μ hμ h hh φ hφ hE
      f t.1.1.1 hf t.2.1 t.2.2.1
    simpa only [weightedOnePairing, oneFormPairing_add_right, add_mul] using integral_add (hi t) (hi v)
  map_smul' c t := by
    change weightedOneInner E g.form μ h φ f (c • t.1.1.1) = c • _
    unfold weightedOneInner
    simp only [weightedOnePairing, oneFormPairing_smul_right, mul_assoc, smul_eq_mul]
    exact integral_const_mul c _

include hE in
/-- Riesz representation with the exact inverse curvature integral bound. -/
theorem exists_compact_joint_riesz_pair
    (hN : WeightedNakanoNonnegative (r := r) E h φ)
    (f : NQForm E 1) (hf : LocallyL2 (r := r) E f)
    (hfinite : inverseCurvatureIntegral (r := r) E g.form h μ φ f < ⊤) :
    ∃ u : WeightedTopHilbert E g μ hμ h hh φ hφ,
      ∃ w : WeightedTwoHilbert E g μ hμ h hh φ hφ,
        ‖u‖ ^ 2 + ‖w‖ ^ 2 ≤ (inverseCurvatureIntegral (r := r) E g.form h μ φ f).toReal ∧
        ∀ t : CompactJointTriple E g μ hμ h hh φ hφ,
          IsCompactJointTriple E g μ hμ h hh φ hφ t →
          inner ℂ u (realizeWeightedTopSection E g μ hμ h hh φ hφ t.2.1) +
            inner ℂ w (realizeWeightedTwoSection E g μ hμ h hh φ hφ t.2.2) =
              weightedOneInner E g.form μ h φ f t.1.1 := by
  have hb (t : compactJointTestSpace E g μ hμ h hh φ hφ) :
      ‖compactJointSource E g μ hμ h hh φ hφ hE f hf t‖ ^ 2 ≤
        (inverseCurvatureIntegral (r := r) E g.form h μ φ f).toReal *
          ‖compactJointLinearMap E g μ hμ h hh φ hφ t‖ ^ 2 := by
    obtain ⟨hU,hcU,hS,_hcS,hD,hcD,hUD,hUS⟩ := t.2
    have hbound := compact_source_joint_graph_bound E g μ hμ h hh φ hφ hE hN f hf hfinite
      t.1.1 hU hcU t.1.2.2 hD hcD hUD t.1.2.1 hS hUS
    simpa only [compactJointSource, LinearMap.coe_mk, AddHom.coe_mk,
      compactJointLinearMap, WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd] using hbound
  obtain ⟨v,hv,hrep⟩ := exists_sq_norm_le_inner_eq_of_range_bound
    (compactJointLinearMap E g μ hμ h hh φ hφ)
    (compactJointSource E g μ hμ h hh φ hφ hE f hf)
    (inverseCurvatureIntegral (r := r) E g.form h μ φ f).toReal ENNReal.toReal_nonneg hb
  refine ⟨(WithLp.ofLp v).1, (WithLp.ofLp v).2, ?_, ?_⟩
  · simpa only [WithLp.prod_norm_sq_eq_of_L2, WithLp.fst, WithLp.snd] using hv
  · intro t ht
    exact hrep ⟨t, ht⟩

end Yau.LeafProofs.L14Aux
