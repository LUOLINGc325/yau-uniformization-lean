import Yau.LeafProofs.L14Realification

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem integral_star_complex {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → ℂ) :
    star (∫ x, f x ∂ν) = ∫ x, star (f x) ∂ν := (integral_conj (f := f)).symm

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

def localDualCoefficient (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (α : Fin r) (c : Fin n × Fin r) (i : Fin n) (z : ComplexVector n) : ℂ :=
  (Real.exp (-inChart a φ z) : ℂ) * (hMat g a z)⁻¹ i c.1 * BundleDbar.metricMatrix (r := r) E h a z α c.2

theorem localDualCoefficient_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (α : Fin r) (c : Fin n × Fin r) (i : Fin n) :
    ContDiffOn ℝ ∞ (localDualCoefficient (r := r) E g.form h φ a α c i) (localDomain (r := r) E a) :=
  (((((hφ a).neg.exp).continuousLinearMap_comp Complex.ofRealCLM).mul
    (L18Aux.hMat_inverse_contDiffOn g a i c.1)).mono Set.inter_subset_left).mul (hh a α c.2)

theorem chartOneDual_eq_flat_sum (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → ComplexVector r) (z : ComplexVector n)
    (i : Fin n) (α : Fin r) :
    chartOneDual (r := r) E g h φ a F z i α =
      ∑ c : Fin n × Fin r, localDualCoefficient (r := r) E g h φ a α c i z * F z c.1 c.2 := by
  simp only [chartOneDual, localDualCoefficient, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, inChart]

theorem memLp_continuousOn_mul_compact
    (K : Set (ComplexVector n)) (hK : IsCompact K) (C f : ComplexVector n → ℂ)
    (hC : ContinuousOn C K) (hf : MemLp f 2 ((lebesgueC n).restrict K)) :
    MemLp (fun z => C z * f z) 2 ((lebesgueC n).restrict K) := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hC
  have hmeas : AEStronglyMeasurable C ((lebesgueC n).restrict K) :=
    hC.aestronglyMeasurable hK.measurableSet
  have htop : MemLp C ∞ ((lebesgueC n).restrict K) := memLp_top_of_bound hmeas B
    ((ae_restrict_mem hK.measurableSet).mono fun z hz => hB z hz)
  exact htop.mul hf

theorem chartOneDual_memLp_compact (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hs : K ⊆ localDomain (r := r) E a)
    (i : Fin n) (α : Fin r) :
    MemLp (fun z => chartOneDual (r := r) E g.form h φ a
      (fun w j => coefficients (r := r) E u a w (fun _ => j)) z i α) 2 ((lebesgueC n).restrict K) := by
  have ht (c : Fin n × Fin r) : MemLp (fun z => localDualCoefficient (r := r) E g.form h φ a α c i z *
      coefficients (r := r) E u a z (fun _ => c.1) c.2) 2 ((lebesgueC n).restrict K) :=
    memLp_continuousOn_mul_compact K hK _ _
      ((localDualCoefficient_contDiffOn E g h hh φ hφ a α c i).continuousOn.mono hs)
      (locallyL2_coefficients_memLp E u hu a (fun _ => c.1) c.2 K hK hs)
  have hsum := memLp_finsetSum Finset.univ (fun c _ => ht c)
  exact MemLp.ae_eq (Eventually.of_forall fun z =>
    (chartOneDual_eq_flat_sum E g.form h φ a
      (fun w j => coefficients (r := r) E u a w (fun _ => j)) z i α).symm) hsum

theorem chartOneDual_locallyIntegrableOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (hu : LocallyL2 (r := r) E u) (a : M.Carrier) (i : Fin n) (α : Fin r) :
    LocallyIntegrableOn (fun z => chartOneDual (r := r) E g.form h φ a
      (fun w j => coefficients (r := r) E u a w (fun _ => j)) z i α)
      (localDomain (r := r) E a) (lebesgueC n) := by
  apply (locallyIntegrableOn_iff (localDomain_isOpen E a).isLocallyClosed).mpr
  intro K hs hK
  letI : IsFiniteMeasure ((lebesgueC n).restrict K) := isFiniteMeasure_restrict.mpr (by
    rw [lebesgueC_eq_volume]; exact hK.measure_lt_top.ne)
  exact (chartOneDual_memLp_compact E g h hh φ hφ u hu a K hK hs i α).integrable (by norm_num)

theorem weightedTopDualCoefficient_memLp_compact
    (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 0) (hu : LocallyL2 (r := r) E u) (a : M.Carrier)
    (K : Set (ComplexVector n)) (hK : IsCompact K) (hs : K ⊆ localDomain (r := r) E a) (α : Fin r) :
    MemLp (fun z => weightedTopDualCoefficient (r := r) E h φ u a z α) 2 ((lebesgueC n).restrict K) := by
  have hρ : ContDiffOn ℝ ∞ (fun z => (Real.exp (-inChart a φ z) : ℂ)) (localDomain (r := r) E a) :=
    (((hφ a).neg.exp).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left
  have ht (β : Fin r) : MemLp (fun z =>
      (BundleDbar.metricMatrix (r := r) E h a z α β * (Real.exp (-inChart a φ z) : ℂ)) *
        coefficients (r := r) E u a z Fin.elim0 β) 2 ((lebesgueC n).restrict K) :=
    memLp_continuousOn_mul_compact K hK _ _ (((hh a α β).mul hρ).continuousOn.mono hs)
      (locallyL2_coefficients_memLp E u hu a Fin.elim0 β K hK hs)
  have hsum := memLp_finsetSum Finset.univ (fun β _ => ht β)
  apply MemLp.ae_eq _ hsum
  apply Eventually.of_forall
  intro z
  simp only [weightedTopDualCoefficient, Finset.sum_mul, inChart]
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem weakDbar_one_component_tests
    (u : NQForm E 1) (f : NQForm E 2) (huf : WeakDbar (r := r) E u f)
    (a : M.Carrier) (i j : Fin n) (α : Fin r) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    (∫ z, coefficients (r := r) E f a z ![i,j] α * ψ z ∂lebesgueC n) =
      -(∫ z, coefficients (r := r) E u a z (fun _ => j) α * wirtBar ψ z (stdVec i) ∂lebesgueC n) +
      (∫ z, coefficients (r := r) E u a z (fun _ => i) α * wirtBar ψ z (stdVec j) ∂lebesgueC n) := by
  have hdel0 : (fun t : Fin 1 => (![i,j] : Fin 2 → Fin n) ((0 : Fin 2).succAbove t)) = (fun _ => j) := by
    ext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  have hdel1 : (fun t : Fin 1 => (![i,j] : Fin 2 → Fin n) ((1 : Fin 2).succAbove t)) = (fun _ => i) := by
    ext t
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl
  have he := huf.2.2 a ![i,j] α ψ hψ hc hs
  change (∫ z, coefficients (r := r) E f a z ![i,j] α * ψ z ∂lebesgueC n) =
    -∑ k : Fin 2, (-1 : ℂ) ^ k.val * ∫ z,
      coefficients (r := r) E u a z (fun l => (![i,j] : Fin 2 → Fin n) (k.succAbove l)) α *
        wirtBar ψ z (stdVec ((![i,j] : Fin 2 → Fin n) k)) ∂lebesgueC n at he
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    hdel0, hdel1, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, neg_one_mul,
    neg_add_rev, neg_neg, add_comm] using he

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem adjoint_graph_scalar_distribution_unconjugated
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (a : M.Carrier) (α : Fin r) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ localDomain (r := r) E a) :
    (∫ z, weightedTopDualCoefficient (r := r) E h φ S.1 a z α * ψ z ∂lebesgueC n) =
      ∫ z, ∑ i, chartOneDual (r := r) E g.form h φ a
        (fun w j => coefficients (r := r) E U.1 a w (fun _ => j)) z i α *
        wirt ψ z (stdVec i) ∂lebesgueC n := by
  let B := chartOneDual (r := r) E g.form h φ a (fun w j => coefficients (r := r) E U.1 a w (fun _ => j))
  have hψs : ContDiff ℝ ∞ (fun z => star (ψ z)) := Complex.conjCLE.contDiff.comp hψ
  have hcs : HasCompactSupport (fun z => star (ψ z)) := hc.comp_left (star_zero ℂ)
  have hss : tsupport (fun z => star (ψ z)) ⊆ localDomain (r := r) E a :=
    (tsupport_comp_subset (g := fun c : ℂ => star c) (star_zero ℂ) ψ).trans hs
  have he := congrArg star (adjoint_graph_scalar_distribution E g μ hμ h hh φ hφ hE
    U S hUS a α (fun z => star (ψ z)) hψs hcs hss)
  have hL : star (∫ z, star (weightedTopDualCoefficient (r := r) E h φ S.1 a z α) * star (ψ z) ∂lebesgueC n) =
      ∫ z, weightedTopDualCoefficient (r := r) E h φ S.1 a z α * ψ z ∂lebesgueC n := by
    rw [integral_star_complex]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simp only [star_mul, star_star, mul_comm]
  have hR : star (∫ z, ∑ i, star (B z i α) * wirtBar (fun z => star (ψ z)) z (stdVec i) ∂lebesgueC n) =
      ∫ z, ∑ i, B z i α * wirt ψ z (stdVec i) ∂lebesgueC n := by
    rw [integral_star_complex]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by simp only [star_sum, star_mul, wirtBar_star, star_star, mul_comm]
  exact hL.symm.trans (he.trans hR)

end Yau.LeafProofs.L14Aux
