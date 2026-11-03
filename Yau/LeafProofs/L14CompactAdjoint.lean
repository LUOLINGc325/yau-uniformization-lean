import Yau.LeafProofs.L14Localize

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

theorem nqForm_finset_sum_value {q : ℕ} {ι : Type*}
    (s : Finset ι) (u : ι → NQForm E q) (x : M.Carrier) :
    ((∑ i ∈ s, u i) x).1 = ∑ i ∈ s, (u i x).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    change (u i x).1 + ((∑ j ∈ s, u j) x).1 = _
    rw [ih]

theorem nqForm_sum_value {q : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → NQForm E q) (x : M.Carrier) :
    ((∑ i, u i) x).1 = ∑ i, (u i x).1 := nqForm_finset_sum_value E Finset.univ u x

theorem smoothForm_zero (q : ℕ) : SmoothForm (r := r) E (0 : NQForm E q) := by
  intro a I α
  simp only [coefficients_zero]
  exact contDiffOn_const

theorem smoothForm_add {q : ℕ} (u v : NQForm E q)
    (hu : SmoothForm (r := r) E u) (hv : SmoothForm (r := r) E v) :
    SmoothForm (r := r) E (u + v) := by
  intro a I α
  simpa only [coefficients_add] using (hu a I α).add (hv a I α)

theorem smoothForm_sum {q : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → NQForm E q) (hu : ∀ i, SmoothForm (r := r) E (u i)) :
    SmoothForm (r := r) E (∑ i, u i) := by
  classical
  have hsum (s : Finset ι) : SmoothForm (r := r) E (∑ i ∈ s, u i) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using smoothForm_zero (r := r) E q
    | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using smoothForm_add E (u i) _ (hu i) ih
  exact hsum Finset.univ

theorem compact_formSupport_sum {q : ℕ} {ι : Type*} [Fintype ι]
    (u : ι → NQForm E q) (hu : ∀ i, IsCompact (closure {x | u i x ≠ (0 : NQForm E q) x})) :
    IsCompact (closure {x | (∑ i, u i) x ≠ (0 : NQForm E q) x}) := by
  have hK : IsCompact (⋃ i, closure {x | u i x ≠ (0 : NQForm E q) x}) := isCompact_iUnion hu
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  have hz (i : ι) : u i x = (0 : NQForm E q) x := by
    by_contra h
    exact hn (Set.mem_iUnion.mpr ⟨i, subset_closure h⟩)
  apply hx
  apply Subtype.ext
  rw [nqForm_sum_value]
  simp only [hz, nqForm_zero_apply, Finset.sum_const_zero]

theorem sum_multiplyForm_eq {q : ℕ} {ι : Type*} [Fintype ι]
    (η : ι → M.Carrier → ℂ) (u : NQForm E q)
    (hη : ∀ x, u x ≠ (0 : NQForm E q) x → ∑ i, η i x = 1) :
    (∑ i, multiplyForm E (η i) u) = u := by
  funext x
  apply Subtype.ext
  rw [nqForm_sum_value]
  change (∑ i, η i x • (u x).1) = (u x).1
  rw [← Finset.sum_smul]
  by_cases hx : u x = (0 : NQForm E q) x
  · rw [hx]
    change (∑ i, η i x) • (0 : MixedTensor E x q) = 0
    exact smul_zero _
  · rw [hη x hx, one_smul]

theorem exists_finite_compact_chart_decomposition (g : Yau.SmoothMetric M)
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x})) :
    ∃ s : Finset M.Carrier, ∃ F : s → ComplexVector n → Fin n → ComplexVector r,
      (∀ i, ContDiff ℝ ∞ (F i) ∧ HasCompactSupport (F i) ∧
        tsupport (F i) ⊆ localDomain (r := r) E (i : M.Carrier)) ∧
      u = ∑ i : s, oneFormPushforward (r := r) E (i : M.Carrier) (F i) := by
  classical
  obtain ⟨s, χ, hχ, hχn, hχo, hχone⟩ := exists_finite_smooth_bundle_square_partition (r := r) E g hc
  let η := fun i : s => fun x => χ i x ^ 2
  have hηs (i : s) : SmoothFn (η i) := L18Aux.smoothFn_pow (hχ i).1 2
  have hηsupport (i : s) : tsupport (η i) ⊆ tsupport (χ i) := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp only [η, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have hηc (i : s) : HasCompactSupport (η i) :=
    (hχ i).2.of_isClosed_subset (isClosed_tsupport _) (hηsupport i)
  have hηo (i : s) : tsupport (η i) ⊆ bundleChartSource (r := r) E (i : M.Carrier) :=
    (hηsupport i).trans (hχo i)
  let F := fun i : s => compactOneChartCoefficients (r := r) E (η i) u (i : M.Carrier)
  refine ⟨s, F, (fun i => compactOneChartCoefficients_properties E (η i) (hηs i) (hηc i)
    u hu (i : M.Carrier) (hηo i)), ?_⟩
  have hsum : (∑ i, multiplyForm E (fun x => (η i x : ℂ)) u) = u := by
    apply sum_multiplyForm_eq E (fun i x => (η i x : ℂ)) u
    intro x hx
    have hreal : (∑ i, χ i x ^ 2) = 1 := (hχone x (subset_closure hx)).self_of_nhds
    exact_mod_cast hreal
  calc
    _ = ∑ i, multiplyForm E (fun x => (η i x : ℂ)) u := hsum.symm
    _ = _ := Finset.sum_congr rfl (fun i _ => multiplyForm_eq_oneFormPushforward E (η i) u
      (i : M.Carrier) (hηo i))

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)

theorem weightedOneSection_sum_val {ι : Type*} [Fintype ι]
    (v : ι → WeightedOneSection E g μ hμ h hh φ hφ) :
    (∑ i, v i).1 = ∑ i, (v i).1 :=
  map_sum (weightedOneFormSubmodule (r := r) E g μ hμ h hh φ hφ).subtype v Finset.univ

theorem weightedTopSection_sum_val {ι : Type*} [Fintype ι]
    (v : ι → WeightedTopSection E g μ hμ h hh φ hφ) :
    (∑ i, v i).1 = ∑ i, (v i).1 :=
  map_sum (weightedTopFormSubmodule (r := r) E g μ hμ h hh φ hφ).subtype v Finset.univ

theorem realizeWeightedOneSection_sum {ι : Type*} [Fintype ι]
    (v : ι → WeightedOneSection E g μ hμ h hh φ hφ) :
    realizeWeightedOneSection E g μ hμ h hh φ hφ (∑ i, v i) =
      ∑ i, realizeWeightedOneSection E g μ hμ h hh φ hφ (v i) :=
  map_sum (UniformSpace.Completion.toCompl : WeightedOneSection E g μ hμ h hh φ hφ →+
    WeightedOneHilbert E g μ hμ h hh φ hφ) v Finset.univ

theorem realizeWeightedTopSection_sum {ι : Type*} [Fintype ι]
    (v : ι → WeightedTopSection E g μ hμ h hh φ hφ) :
    realizeWeightedTopSection E g μ hμ h hh φ hφ (∑ i, v i) =
      ∑ i, realizeWeightedTopSection E g μ hμ h hh φ hφ (v i) :=
  map_sum (UniformSpace.Completion.toCompl : WeightedTopSection E g μ hμ h hh φ hφ →+
    WeightedTopHilbert E g μ hμ h hh φ hφ) v Finset.univ

variable (hE : Holomorphic (r := r) E)

include hE

theorem weightedDbarAdjointChartSection_smooth_compact
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ localDomain (r := r) E a) :
    let S := weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE a F hF hc hs
    SmoothForm (r := r) E S.1 ∧ IsCompact (closure {x | S.1 x ≠ (0 : NQForm E 0) x}) := by
  let δ := chartDbarAdjoint (r := r) E g.form h φ a F
  have hδ : ContDiff ℝ ∞ δ := chartDbarAdjoint_contDiff E g h hh φ hφ a F hF hs
  have hδs : tsupport δ ⊆ localDomain (r := r) E a := (tsupport_chartDbarAdjoint_subset E g.form h φ a F).trans hs
  have hδc : HasCompactSupport δ := hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartDbarAdjoint_subset E g.form h φ a F)
  refine ⟨topFormPushforward_smooth E hE a δ hδ hδc hδs, ?_⟩
  have hK : IsCompact (chartInv a '' tsupport δ) := hδc.image_of_continuousOn
    ((continuousOn_extChartAt_symm (I := ComplexModel n) a).mono (hδs.trans Set.inter_subset_left))
  exact hK.of_isClosed_subset isClosed_closure (topFormPushforward_support E a δ hδc hδs)

theorem smooth_compact_oneForm_has_adjoint
    (u : NQForm E 1) (hu : SmoothForm (r := r) E u)
    (hc : IsCompact (closure {x | u x ≠ (0 : NQForm E 1) x})) :
    let U : WeightedOneSection E g μ hμ h hh φ hφ :=
      ⟨u, smooth_compact_weightedL2_one E g μ hμ h hh φ hφ u hu hc⟩
    ∃ S : WeightedTopSection E g μ hμ h hh φ hφ,
      SmoothForm (r := r) E S.1 ∧ IsCompact (closure {x | S.1 x ≠ (0 : NQForm E 0) x}) ∧
        (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
          realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
            (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph := by
  classical
  let U : WeightedOneSection E g μ hμ h hh φ hφ :=
    ⟨u, smooth_compact_weightedL2_one E g μ hμ h hh φ hφ u hu hc⟩
  obtain ⟨s, F, hF, hdecomp⟩ := exists_finite_compact_chart_decomposition E g u hu hc
  let V := fun i : s => weightedOneChartSection E g μ hμ h hh φ hφ hE (i : M.Carrier)
    (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  let S := fun i : s => weightedDbarAdjointChartSection E g μ hμ h hh φ hφ hE (i : M.Carrier)
    (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hsumV : (∑ i, V i) = U := by
    apply Subtype.ext
    change (∑ i, V i).1 = u
    rw [weightedOneSection_sum_val]
    exact hdecomp.symm
  have hgraph : (∑ i, (realizeWeightedOneSection E g μ hμ h hh φ hφ (V i),
      realizeWeightedTopSection E g μ hμ h hh φ hφ (S i))) ∈
        (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph := by
    apply Submodule.sum_mem
    intro i _
    exact weightedMaximalDbar_adjoint_chart E g μ hμ h hh φ hφ hE (i : M.Carrier)
      (F i) (hF i).1 (hF i).2.1 (hF i).2.2
  have hpair : (∑ i, (realizeWeightedOneSection E g μ hμ h hh φ hφ (V i),
      realizeWeightedTopSection E g μ hμ h hh φ hφ (S i))) =
      (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
        realizeWeightedTopSection E g μ hμ h hh φ hφ (∑ i, S i)) := by
    ext
    · simp only [Prod.fst_sum]
      rw [← realizeWeightedOneSection_sum E g μ hμ h hh φ hφ V, hsumV]
    · simp only [Prod.snd_sum]
      exact (realizeWeightedTopSection_sum E g μ hμ h hh φ hφ S).symm
  rw [hpair] at hgraph
  refine ⟨∑ i, S i, ?_, ?_, hgraph⟩
  · rw [weightedTopSection_sum_val]
    exact smoothForm_sum E (fun i => (S i).1) (fun i =>
      (weightedDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE (i : M.Carrier)
        (F i) (hF i).1 (hF i).2.1 (hF i).2.2).1)
  · rw [weightedTopSection_sum_val]
    exact compact_formSupport_sum E (fun i => (S i).1) (fun i =>
      (weightedDbarAdjointChartSection_smooth_compact E g μ hμ h hh φ hφ hE (i : M.Carrier)
        (F i) (hF i).1 (hF i).2.1 (hF i).2.2).2)

end Yau.LeafProofs.L14Aux
