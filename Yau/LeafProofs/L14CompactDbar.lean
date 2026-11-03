import Yau.LeafProofs.L14CompactAdjoint

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem coefficients_sum {q : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → NQForm E q) (a : M.Carrier) (z : ComplexVector n) (I : Fin q → Fin n) (α : Fin r) :
    coefficients (r := r) E (∑ i, u i) a z I α = ∑ i, coefficients (r := r) E (u i) a z I α := by
  classical
  have hsum (s : Finset ι) : coefficients (r := r) E (∑ i ∈ s, u i) a z I α =
      ∑ i ∈ s, coefficients (r := r) E (u i) a z I α := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using coefficients_zero (r := r) E a z I α
    | @insert i s hi ih => rw [Finset.sum_insert hi, coefficients_add, ih, Finset.sum_insert hi]
  exact hsum Finset.univ

theorem dbarCoefficients_sum {q : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → NQForm E q) (hu : ∀ i, SmoothForm (r := r) E (u i))
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (I : Fin (q + 1) → Fin n) (α : Fin r) :
    dbarCoefficients (r := r) E (∑ i, u i) a z I α =
      ∑ i, dbarCoefficients (r := r) E (u i) a z I α := by
  have hw (k : Fin (q + 1)) :
      wirtBar (fun w => ∑ i, coefficients (r := r) E (u i) a w (fun l => I (k.succAbove l)) α)
        z (stdVec (I k)) = ∑ i, wirtBar
          (fun w => coefficients (r := r) E (u i) a w (fun l => I (k.succAbove l)) α) z (stdVec (I k)) := by
    apply wirtBar_sum_fun Finset.univ
    intro i _
    exact ((hu i a (fun l => I (k.succAbove l)) α).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  unfold dbarCoefficients
  simp_rw [coefficients_sum, hw, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem smoothDbarRepresents_sum {q : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → NQForm E q) (f : ι → NQForm E (q + 1))
    (hu : ∀ i, SmoothForm (r := r) E (u i))
    (hD : ∀ i, SmoothDbarRepresents (r := r) E (u i) (f i)) :
    SmoothDbarRepresents (r := r) E (∑ i, u i) (∑ i, f i) := by
  intro a z hz I α
  rw [coefficients_sum, dbarCoefficients_sum E u hu a z hz I α]
  exact Finset.sum_congr rfl (fun i _ => hD i a z hz I α)

theorem twoFormPushforward_compact (a : M.Carrier)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ localDomain (r := r) E a) :
    IsCompact (closure {x | twoFormPushforward (r := r) E a F x ≠ (0 : NQForm E 2) x}) := by
  have hK : IsCompact (chartInv a '' tsupport F) := hc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hs.trans Set.inter_subset_left))
  exact hK.of_isClosed_subset isClosed_closure (twoFormPushforward_support E a F hc hs)

theorem smooth_compact_oneForm_has_dbar
    (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ) (hE : Holomorphic (r := r) E)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x})) :
    ∃ f : NQForm E 2, SmoothForm (r := r) E f ∧
      IsCompact (closure {x | f x ≠ (0 : NQForm E 2) x}) ∧
      SmoothDbarRepresents (r := r) E u f ∧ MaximalDbarGraph (r := r) E g.form h μ φ u f := by
  classical
  obtain ⟨s, F, hF, hdecomp⟩ := exists_finite_compact_chart_decomposition E g u hu hc
  let U := fun i : s => oneFormPushforward (r := r) E (i : M.Carrier) (F i)
  let D := fun i : s => twoFormPushforward (r := r) E (i : M.Carrier) (modelOneDbar (F i))
  have hUs (i : s) : SmoothForm (r := r) E (U i) :=
    oneFormPushforward_smooth E hE (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hDs (i : s) : SmoothForm (r := r) E (D i) :=
    twoFormPushforward_modelOneDbar_smooth E hE (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hDc (i : s) : IsCompact (closure {x | D i x ≠ (0 : NQForm E 2) x}) :=
    twoFormPushforward_compact E (i : M.Carrier) (modelOneDbar (F i))
      ((hF i).2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_modelOneDbar_subset (F i)))
      ((tsupport_modelOneDbar_subset (F i)).trans (hF i).2.2)
  have hD : SmoothDbarRepresents (r := r) E u (∑ i, D i) := by
    rw [hdecomp]
    exact smoothDbarRepresents_sum E U D hUs (fun i => oneFormPushforward_representsDbar E hE
      (i : M.Carrier) (F i) (hF i).1 (hF i).2.1 (hF i).2.2)
  have hfs : SmoothForm (r := r) E (∑ i, D i) := smoothForm_sum E D hDs
  have hfc : IsCompact (closure {x | (∑ i, D i) x ≠ (0 : NQForm E 2) x}) := compact_formSupport_sum E D hDc
  refine ⟨∑ i, D i, hfs, hfc, hD, ?_⟩
  exact ⟨smooth_compact_weightedL2_one E g μ hμ h hh φ hφ u hu hc,
    smooth_compact_weightedL2_two E g μ hμ h hh φ hφ _ hfs hfc,
    weakDbar_of_smooth_isDbarOf_degree E u _ hu hfs hD⟩

end Yau.LeafProofs.L14Aux
