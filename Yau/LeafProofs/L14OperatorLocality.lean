import Yau.LeafProofs.L14ChartBKN

set_option backward.isDefEq.respectTransparency false

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

theorem coefficients_eventually_zero_off_support {q : ℕ} (u : NQForm E q)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a)
    (hx : chartInv a z ∉ closure {x | u x ≠ (0 : NQForm E q) x}) (I : Fin q → Fin n) (α : Fin r) :
    (fun w => coefficients (r := r) E u a w I α) =ᶠ[𝓝 z] (fun _ => 0) := by
  have hnear : ∀ᶠ y in 𝓝 (chartInv a z), u y = (0 : NQForm E q) y := by
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    by_contra hn
    exact hy (subset_closure hn)
  have ht := (continuousAt_extChartAt_symm'' (I := ComplexModel n) hz).tendsto.eventually hnear
  filter_upwards [ht] with w hw
  exact coefficients_eq_zero_of_value_zero E u a w hw I α

theorem dbarCoefficients_eq_zero_off_support {q : ℕ} (u : NQForm E q)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a)
    (hx : chartInv a z ∉ closure {x | u x ≠ (0 : NQForm E q) x})
    (I : Fin (q + 1) → Fin n) (α : Fin r) : dbarCoefficients (r := r) E u a z I α = 0 := by
  have hd (k : Fin (q + 1)) :
      wirtBar (fun w => coefficients (r := r) E u a w (fun j => I (k.succAbove j)) α) z (stdVec (I k)) = 0 := by
    have he := coefficients_eventually_zero_off_support E u a z hz hx (fun j => I (k.succAbove j)) α
    unfold wirtBar
    rw [he.fderiv_eq]
    simp
  simp only [dbarCoefficients, hd, mul_zero, Finset.sum_const_zero]

theorem chartDbarAdjoint_eq_zero_off_support (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (u : NQForm E 1)
    (a : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget a)
    (hx : chartInv a z ∉ closure {x | u x ≠ (0 : NQForm E 1) x}) :
    chartDbarAdjoint (r := r) E g h φ a
      (fun w i => coefficients (r := r) E u a w (fun _ => i)) z = 0 := by
  have he (i : Fin n) (α : Fin r) : (fun w => chartOneDual (r := r) E g h φ a
      (fun y j => coefficients (r := r) E u a y (fun _ => j)) w i α) =ᶠ[𝓝 z] (fun _ => 0) := by
    have hall : ∀ᶠ w in 𝓝 z, ∀ j β, coefficients (r := r) E u a w (fun _ => j) β = 0 :=
      eventually_all.mpr (fun j => eventually_all.mpr (fun β =>
        coefficients_eventually_zero_off_support E u a z hz hx (fun _ => j) β))
    filter_upwards [hall] with w hw
    simp only [chartOneDual, hw, mul_zero, Finset.sum_const_zero]
  have hd (i : Fin n) (α : Fin r) :
      wirt (fun w => chartOneDual (r := r) E g h φ a
        (fun y j => coefficients (r := r) E u a y (fun _ => j)) w i α) z (stdVec i) = 0 := by
    unfold wirt
    rw [(he i α).fderiv_eq]
    simp
  ext α
  simp only [chartDbarAdjoint, WithLp.ofLp_toLp, hd, Finset.sum_const_zero, mul_zero, PiLp.zero_apply]

theorem closure_formSupport_multiply_subset {q : ℕ} (η : M.Carrier → ℂ) (u : NQForm E q) :
    closure {x | multiplyForm E η u x ≠ (0 : NQForm E q) x} ⊆
      closure {x | u x ≠ (0 : NQForm E q) x} := by
  apply closure_mono
  intro x hx hu
  apply hx
  apply Subtype.ext
  change η x • (u x).1 = 0
  rw [hu]
  change η x • (0 : MixedTensor E x q) = 0
  exact smul_zero _

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

include hE in
theorem bknResidual_eq_zero_off_support
    (U : WeightedOneSection E g μ hμ h hh φ hφ) (hU : SmoothForm (r := r) E U.1)
    (f : NQForm E 2) (hdu : SmoothDbarRepresents (r := r) E U.1 f)
    (S : WeightedTopSection E g μ hμ h hh φ hφ) (hS : SmoothForm (r := r) E S.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (x : M.Carrier) (hx : x ∉ closure {y | U.1 y ≠ (0 : NQForm E 1) y}) :
    bknResidual (r := r) E g.form h φ U.1 f S.1 x = 0 := by
  let z := chartPt x x
  have hInv : chartInv x z = x := chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hz : z ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x z ∈ (localTriv (r := r) E x).baseSet
    rw [hInv]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hxz : chartInv x z ∉ closure {y | U.1 y ≠ (0 : NQForm E 1) y} := by rw [hInv]; exact hx
  have hf (i j : Fin n) (α : Fin r) : coefficients (r := r) E f x z ![i,j] α = 0 := by
    rw [hdu x z hz ![i,j] α]
    exact dbarCoefficients_eq_zero_off_support E U.1 x z hz.1 hxz ![i,j] α
  have hδ : coefficients (r := r) E S.1 x z Fin.elim0 = 0 :=
    (smooth_adjoint_local_formula E g μ hμ h hh φ hφ hE U S hU hS hUS x z hz).trans
      (chartDbarAdjoint_eq_zero_off_support E g.form h φ U.1 x z hz.1 hxz)
  have hfn := formNormSq_two_chart_factor E g.form h f x z hz
  have hSn := formNormSq_top_inChart E g.form h S.1 x z hz
  rw [hInv] at hfn hSn
  have hSf (α : Fin r) : coefficients (r := r) E S.1 x z Fin.elim0 α = 0 := by rw [hδ]; rfl
  simp only [hf, hSf, star_zero, zero_mul, mul_zero, Finset.sum_const_zero, Complex.zero_re] at hfn hSn
  have hux : U.1 x = (0 : NQForm E 1) x := by
    by_contra hn
    exact hx (subset_closure hn)
  rw [bknResidual, bknDifferentialEnergy, hfn, hSn,
    positiveFormEnergy_eq_zero_off_support E g.form h φ U.1 x hx,
    curvatureFormEnergy_eq_zero_of_value_zero E g.form h φ U.1 x hux]
  ring

theorem curvatureFormEnergy_multiply_real (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (χ : M.Carrier → ℝ) (u : NQForm E 1) (x : M.Carrier) :
    curvatureFormEnergy (r := r) E g h φ (multiplyForm E (fun x => (χ x : ℂ)) u) x =
      χ x ^ 2 * curvatureFormEnergy (r := r) E g h φ u x := by
  have hInv : chartInv x (chartPt x x) = x := chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hc : (fun i α => coefficients (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) u)
      x (chartPt x x) (fun _ => i) α) =
      (χ x : ℂ) • (fun i α => coefficients (r := r) E u x (chartPt x x) (fun _ => i) α) := by
    ext i α
    rw [coefficients_multiplyForm, hInv]
    rfl
  rw [curvatureFormEnergy, hc, curvatureEnergy_smul]
  simp only [Complex.normSq_ofReal, curvatureFormEnergy, pow_two]
  ring

end Yau.LeafProofs.L14Aux
