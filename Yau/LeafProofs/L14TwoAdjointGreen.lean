import Yau.LeafProofs.L14TwoAdjointModel
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module
namespace Yau.LeafProofs.L14Aux
open BundleDbar

theorem wirt_fun_neg {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : X → ℂ) (z v : X) : wirt (fun w => -f w) z v = -wirt f z v := by
  unfold wirt
  rw [fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]
  ring

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem weakDbar_one_component_star_tests
    (u : NQForm E 1) (f : NQForm E 2) (huf : WeakDbar (r := r) E u f)
    (a : M.Carrier) (i j : Fin n) (α : Fin r) (ψ : ComplexVector n → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ localDomain (r := r) E a) :
    (∫ z, star (coefficients (r := r) E f a z ![i,j] α) * ψ z ∂lebesgueC n) =
      -(∫ z, star (coefficients (r := r) E u a z (fun _ => j) α) * wirt ψ z (stdVec i) ∂lebesgueC n) +
      (∫ z, star (coefficients (r := r) E u a z (fun _ => i) α) * wirt ψ z (stdVec j) ∂lebesgueC n) := by
  have hstar : ContDiff ℝ ∞ (fun z => star (ψ z)) := Complex.conjCLE.contDiff.comp hψ
  have hcstar : HasCompactSupport (fun z => star (ψ z)) := hcψ.comp_left (star_zero _)
  have hsstar : tsupport (fun z => star (ψ z)) ⊆ localDomain (r := r) E a :=
    (tsupport_comp_subset (g := fun c : ℂ => star c) (star_zero _) ψ).trans hsψ
  have he := congrArg star (weakDbar_one_component_tests E u f huf a i j α
    (fun z => star (ψ z)) hstar hcstar hsstar)
  simpa only [star_add, star_neg, integral_star_complex, star_mul, star_star, wirtBar_star, mul_comm] using he

/-- The antisymmetry of the actual degree-two metric dual cancels the factor
one half in the distributional integration-by-parts identity. -/
theorem weakDbar_two_dual_integral
    (g : Yau.SmoothMetric M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (f : NQForm E 2) (huf : WeakDbar (r := r) E u f)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a)
    (hskew : ∀ z i j, F z j i = -F z i j) :
    (1 / 2 : ℂ) * (∑ i, ∑ j, ∑ α,
      ∫ z, star (coefficients (r := r) E f a z ![i,j] α) * chartTwoDual E g.form h φ a F z i j α ∂lebesgueC n) =
      -(∑ i, ∑ j, ∑ α, ∫ z, star (coefficients (r := r) E u a z (fun _ => j) α) *
        wirt (fun w => chartTwoDual E g.form h φ a F w i j α) z (stdVec i) ∂lebesgueC n) := by
  classical
  let B := chartTwoDual E g.form h φ a F
  have hB (i j : Fin n) (α : Fin r) : ContDiff ℝ ∞ (fun z => B z i j α) :=
    chartTwoDual_contDiff E g h hh φ hφ a F hF hsF i j α
  have hsB (i j : Fin n) (α : Fin r) : tsupport (fun z => B z i j α) ⊆ tsupport F :=
    tsupport_chartTwoDual_subset E g.form h φ a F i j α
  have hcB (i j : Fin n) (α : Fin r) : HasCompactSupport (fun z => B z i j α) :=
    hcF.of_isClosed_subset (isClosed_tsupport _) (hsB i j α)
  have he (i j : Fin n) (α : Fin r) := weakDbar_one_component_star_tests E u f huf a i j α
    (fun z => B z i j α) (hB i j α) (hcB i j α) ((hsB i j α).trans hsF)
  have hneg (i j : Fin n) (α : Fin r) : (fun z => B z i j α) = fun z => -B z j i α :=
    funext fun z => chartTwoDual_skew E g.form h φ a F z (hskew z) j i α
  have hsecond (i j : Fin n) (α : Fin r) :
      (∫ z, star (coefficients (r := r) E u a z (fun _ => i) α) * wirt (fun w => B w i j α) z (stdVec j) ∂lebesgueC n) =
      -(∫ z, star (coefficients (r := r) E u a z (fun _ => i) α) * wirt (fun w => B w j i α) z (stdVec j) ∂lebesgueC n) := by
    simp_rw [hneg i j α, wirt_fun_neg, mul_neg]
    exact integral_neg _
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_congr rfl (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      Finset.sum_congr rfl (fun α (_ : α ∈ (Finset.univ : Finset (Fin r))) => he i j α)))
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hsum
  simp_rw [hsecond, Finset.sum_neg_distrib] at hsum
  have hswap : (∑ i, ∑ j, ∑ α, ∫ z, star (coefficients (r := r) E u a z (fun _ => i) α) *
      wirt (fun w => B w j i α) z (stdVec j) ∂lebesgueC n) =
      ∑ i, ∑ j, ∑ α, ∫ z, star (coefficients (r := r) E u a z (fun _ => j) α) *
        wirt (fun w => B w i j α) z (stdVec i) ∂lebesgueC n := Finset.sum_comm
  rw [hswap] at hsum
  change (1 / 2 : ℂ) * (∑ i, ∑ j, ∑ α, ∫ z, star (coefficients (r := r) E f a z ![i,j] α) * B z i j α ∂lebesgueC n) = _
  rw [hsum]
  ring

theorem locallyL2_star_test_integrable {q : ℕ}
    (u : NQForm E q) (hu : LocallyL2 (r := r) E u)
    (a : M.Carrier) (I : Fin q → Fin n) (α : Fin r)
    (ψ : ComplexVector n → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ localDomain (r := r) E a) :
    Integrable (fun z => star (coefficients (r := r) E u a z I α) * ψ z) (lebesgueC n) := by
  have hi := locallyL2_test_integrable E u hu a I α (fun z => star (ψ z))
    (continuous_star.comp hψ) (hcψ.comp_left (star_zero _))
    ((tsupport_comp_subset (g := fun c : ℂ => star c) (star_zero _) ψ).trans hsψ)
  have hs := Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  change Integrable (fun z => star (coefficients (r := r) E u a z I α * star (ψ z))) (lebesgueC n) at hs
  simpa only [star_mul, star_star, mul_comm] using hs

theorem chartTwoDbarAdjoint_dual_global (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hsF : tsupport F ⊆ localDomain (r := r) E a) (z : ComplexVector n) (j : Fin n) (α : Fin r) :
    chartOneDual (r := r) E g h φ a (chartTwoDbarAdjoint E g h φ a F) z j α =
      -∑ i, wirt (fun w => chartTwoDual E g h φ a F w i j α) z (stdVec i) := by
  by_cases hz : z ∈ localDomain (r := r) E a
  · exact chartTwoDbarAdjoint_dual E g h φ a F z hz j α
  · have hn : z ∉ tsupport F := fun hs => hz (hsF hs)
    have hR : chartTwoDbarAdjoint E g h φ a F z = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hn (tsupport_chartTwoDbarAdjoint_subset E g h φ a F hs))
    have hD (i : Fin n) : wirt (fun w => chartTwoDual E g h φ a F w i j α) z (stdVec i) = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => wirt (fun w => chartTwoDual E g h φ a F w i j α) y (stdVec i))
        (fun hs => hn ((tsupport_wirt_subset _ _).trans (tsupport_chartTwoDual_subset E g h φ a F i j α) hs))
    simp only [chartOneDual, hR, hD, Pi.zero_apply, PiLp.zero_apply, mul_zero, Finset.sum_const_zero, neg_zero]

/-- Actual coefficient Green identity for the computed degree-two formal
adjoint; the input graph is only distributional and locally square integrable. -/
theorem weakDbar_chartTwo_adjoint_pairing
    (g : Yau.SmoothMetric M) (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h)
    (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (u : NQForm E 1) (f : NQForm E 2) (huf : WeakDbar (r := r) E u f)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F) (hsF : tsupport F ⊆ localDomain (r := r) E a)
    (hskew : ∀ z i j, F z j i = -F z i j) :
    (1 / 2 : ℂ) * (∑ i, ∑ j, ∑ α,
      ∫ z, star (coefficients (r := r) E f a z ![i,j] α) * chartTwoDual E g.form h φ a F z i j α ∂lebesgueC n) =
      ∑ j, ∑ α, ∫ z, star (coefficients (r := r) E u a z (fun _ => j) α) *
        chartOneDual (r := r) E g.form h φ a (chartTwoDbarAdjoint E g.form h φ a F) z j α ∂lebesgueC n := by
  classical
  let B := chartTwoDual E g.form h φ a F
  have hB (i j : Fin n) (α : Fin r) : ContDiff ℝ ∞ (fun z => B z i j α) :=
    chartTwoDual_contDiff E g h hh φ hφ a F hF hsF i j α
  have hsD (i j : Fin n) (α : Fin r) :
      tsupport (fun z => wirt (fun w => B w i j α) z (stdVec i)) ⊆ tsupport F :=
    (tsupport_wirt_subset _ _).trans (tsupport_chartTwoDual_subset E g.form h φ a F i j α)
  have hD (i j : Fin n) (α : Fin r) : ContDiff ℝ ∞ (fun z => wirt (fun w => B w i j α) z (stdVec i)) := by
    simpa only [contDiffOn_univ] using wirt_contDiffOn isOpen_univ _ (hB i j α).contDiffOn (stdVec i)
  have hi (i j : Fin n) (α : Fin r) : Integrable (fun z => star (coefficients (r := r) E u a z (fun _ => j) α) *
      wirt (fun w => B w i j α) z (stdVec i)) (lebesgueC n) :=
    locallyL2_star_test_integrable E u huf.1 a (fun _ => j) α _ (hD i j α).continuous
      (hcF.of_isClosed_subset (isClosed_tsupport _) (hsD i j α)) ((hsD i j α).trans hsF)
  have hlocal (j : Fin n) (α : Fin r) :
      (∫ z, star (coefficients (r := r) E u a z (fun _ => j) α) *
        chartOneDual (r := r) E g.form h φ a (chartTwoDbarAdjoint E g.form h φ a F) z j α ∂lebesgueC n) =
      -∑ i, ∫ z, star (coefficients (r := r) E u a z (fun _ => j) α) *
        wirt (fun w => B w i j α) z (stdVec i) ∂lebesgueC n := by
    have he : (fun z => star (coefficients (r := r) E u a z (fun _ => j) α) *
        chartOneDual (r := r) E g.form h φ a (chartTwoDbarAdjoint E g.form h φ a F) z j α) =
        fun z => -(∑ i, star (coefficients (r := r) E u a z (fun _ => j) α) *
          wirt (fun w => B w i j α) z (stdVec i)) := by
      funext z
      rw [chartTwoDbarAdjoint_dual_global E g.form h φ a F hsF z j α, mul_neg, Finset.mul_sum]
    rw [he, integral_neg, integral_finsetSum Finset.univ (fun i _ => hi i j α)]
  rw [weakDbar_two_dual_integral E g h hh φ hφ u f huf a F hF hcF hsF hskew]
  simp_rw [hlocal, Finset.sum_neg_distrib]
  congr 1
  calc
    _ = ∑ j, ∑ i, ∑ α, ∫ z, star (coefficients (r := r) E u a z (fun _ => j) α) *
        wirt (fun w => B w i j α) z (stdVec i) ∂lebesgueC n := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_comm

end Yau.LeafProofs.L14Aux
