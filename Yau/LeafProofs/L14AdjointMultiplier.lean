import Yau.LeafProofs.L14AdjointLocal
import Yau.LeafProofs.L14Contraction

noncomputable section
open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix Kronecker
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

variable (g : Yau.SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
  (h : Metric E) (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
  (hE : Holomorphic (r := r) E)

set_option backward.isDefEq.respectTransparency false in
theorem chartDbarAdjoint_mul_scalar_local (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (η : ComplexVector n → ℂ)
    (F : ComplexVector n → Fin n → ComplexVector r)
    (hF : ∀ i α, ContDiffOn ℝ ∞ (fun y => F y i α) (localDomain (r := r) E a))
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (hη : DifferentiableAt ℝ η z) :
    chartDbarAdjoint (r := r) E g.form h φ a (fun y k => η y • F y k) z =
      η z • chartDbarAdjoint (r := r) E g.form h φ a F z -
        WithLp.toLp 2 (fun α => ∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α) := by
  let B := chartOneDual (r := r) E g.form h φ a F
  let H := BundleDbar.metricMatrix (r := r) E h a z
  let c : ℂ := Real.exp (φ (chartInv a z))
  let ρ : ℂ := Real.exp (-φ (chartInv a z))
  have hρ : c * ρ = 1 := by
    dsimp only [c, ρ]
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hd (i : Fin n) (β : Fin r) : DifferentiableAt ℝ (fun y => B y i β) z :=
    ((chartOneDual_contDiffOn E g h hh φ hφ a F hF i β).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  have hder (i : Fin n) (β : Fin r) :
      wirt (fun y => chartOneDual (r := r) E g.form h φ a (fun t k => η t • F t k) y i β) z (stdVec i) =
        wirt η z (stdVec i) * B z i β + η z * wirt (fun y => B y i β) z (stdVec i) := by
    simp_rw [chartOneDual_mul_scalar]
    exact wirt_mul_rule η _ z (stdVec i) hη (hd i β)
  ext α
  change -c * (∑ β, H⁻¹ α β * ∑ i,
      wirt (fun y => chartOneDual (r := r) E g.form h φ a (fun t k => η t • F t k) y i β) z (stdVec i)) =
    η z * (-c * (∑ β, H⁻¹ α β * ∑ i, wirt (fun y => B y i β) z (stdVec i))) -
      ∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α
  simp_rw [hder, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
  have hfirst : (∑ β, H⁻¹ α β * ∑ i, wirt η z (stdVec i) * B z i β) =
      ρ * ∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α := by
    calc
      _ = ∑ i, wirt η z (stdVec i) * ∑ β, H⁻¹ α β * B z i β := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro β _
        ring
      _ = ∑ i, wirt η z (stdVec i) * (ρ * chartOneRaise g.form a F z i α) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [chartOneDual_inverse E g.form h φ a F z hz i α]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
  have hsecond : (∑ β, H⁻¹ α β * ∑ i, η z * wirt (fun y => B y i β) z (stdVec i)) =
      η z * (∑ β, H⁻¹ α β * ∑ i, wirt (fun y => B y i β) z (stdVec i)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfirst, hsecond]
  calc
    _ = η z * (-c * (∑ β, H⁻¹ α β * ∑ i, wirt (fun y => B y i β) z (stdVec i))) -
        (c * ρ) * (∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α) := by ring
    _ = _ := by rw [hρ, one_mul]


theorem smoothForm_multiply_real {q : ℕ} (χ : M.Carrier → ℝ) (hχ : SmoothFn χ)
    (u : NQForm E q) (hu : SmoothForm (r := r) E u) :
    SmoothForm (r := r) E (multiplyForm E (fun x => (χ x : ℂ)) u) := by
  intro a I α
  simp only [coefficients_multiplyForm]
  exact (((hχ a).continuousLinearMap_comp Complex.ofRealCLM).mono Set.inter_subset_left).mul (hu a I α)

theorem compact_formSupport_multiply {q : ℕ} (χ : M.Carrier → ℝ) (hc : HasCompactSupport χ)
    (u : NQForm E q) :
    IsCompact (closure {x | multiplyForm E (fun x => (χ x : ℂ)) u x ≠ (0 : NQForm E q) x}) := by
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hx
  apply Subtype.ext
  change (χ x : ℂ) • (u x).1 = 0
  rw [hz, Complex.ofReal_zero, zero_smul]

theorem topForm_ext (u v : NQForm E 0)
    (he : ∀ a z, z ∈ localDomain (r := r) E a →
      coefficients (r := r) E u a z Fin.elim0 = coefficients (r := r) E v a z Fin.elim0) : u = v := by
  funext x
  have hz : chartPt x x ∈ localDomain (r := r) E x := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    change chartInv x (chartPt x x) ∈ (localTriv (r := r) E x).baseSet
    rw [chartInv_chartPt_of_mem x x (mem_chart_source _ _)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have hp : u (chartInv x (chartPt x x)) = v (chartInv x (chartPt x x)) := by
    apply (topTensorCoordinatesEquiv E x (chartInv x (chartPt x x))
      ⟨(extChartAt (ComplexModel n) x).map_target hz.1, hz.2⟩).injective
    rw [topTensorCoordinatesEquiv_form E u x _ hz, topTensorCoordinatesEquiv_form E v x _ hz]
    exact he x _ hz
  have hxx : chartInv x (chartPt x x) = x := chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  exact (congrArg (fun y => u y = v y) hxx).mp hp

theorem coefficients_sub {q : ℕ} (u v : NQForm E q) (a : M.Carrier)
    (z : ComplexVector n) (I : Fin q → Fin n) (α : Fin r) :
    coefficients (r := r) E (u - v) a z I α =
      coefficients (r := r) E u a z I α - coefficients (r := r) E v a z I α := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ v, coefficients_add, coefficients_smul]
  ring

include hE in
theorem smooth_compact_adjoint_multiplier
    (U : WeightedOneSection E g μ hμ h hh φ hφ)
    (S : WeightedTopSection E g μ hμ h hh φ hφ)
    (hU : SmoothForm (r := r) E U.1) (hS : SmoothForm (r := r) E S.1)
    (hUS : (realizeWeightedOneSection E g μ hμ h hh φ hφ U,
      realizeWeightedTopSection E g μ hμ h hh φ hφ S) ∈
      (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph)
    (χ : M.Carrier → ℝ) (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ) :
    let v := multiplyForm E (fun x => (χ x : ℂ)) U.1
    let V : WeightedOneSection E g μ hμ h hh φ hφ := ⟨v,
      smooth_compact_weightedL2_one E g μ hμ h hh φ hφ v
        (smoothForm_multiply_real E χ hχ U.1 hU) (compact_formSupport_multiply E χ hcχ U.1)⟩
    ∃ R : WeightedTopSection E g μ hμ h hh φ hφ,
      SmoothForm (r := r) E R.1 ∧ IsCompact (closure {x | R.1 x ≠ (0 : NQForm E 0) x}) ∧
      (realizeWeightedOneSection E g μ hμ h hh φ hφ V,
        realizeWeightedTopSection E g μ hμ h hh φ hφ R) ∈
        (weightedMaximalDbar E g μ hμ h hh φ hφ).adjoint.graph ∧
      R.1 = multiplyForm E (fun x => (χ x : ℂ)) S.1 - scalarGradientContraction (r := r) E g.form χ U.1 := by
  classical
  let v := multiplyForm E (fun x => (χ x : ℂ)) U.1
  have hv := smoothForm_multiply_real (r := r) E χ hχ U.1 hU
  have hvc := compact_formSupport_multiply E χ hcχ U.1
  let V : WeightedOneSection E g μ hμ h hh φ hφ :=
    ⟨v, smooth_compact_weightedL2_one E g μ hμ h hh φ hφ v hv hvc⟩
  obtain ⟨R, hR, hcR, hVR⟩ := smooth_compact_oneForm_has_adjoint E g μ hμ h hh φ hφ hE v hv hvc
  refine ⟨R, hR, hcR, hVR, ?_⟩
  apply topForm_ext (r := r) E
  intro a z hz
  have hRF := smooth_adjoint_local_formula E g μ hμ h hh φ hφ hE V R hv hR hVR a z hz
  have hSF := smooth_adjoint_local_formula E g μ hμ h hh φ hφ hE U S hU hS hUS a z hz
  let F := fun w i => coefficients (r := r) E U.1 a w (fun _ => i)
  let η := fun w => Complex.ofReal (inChart a χ w)
  have hη : DifferentiableAt ℝ η z :=
    ((((hχ a).continuousLinearMap_comp Complex.ofRealCLM).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds hz.1))).differentiableAt (by simp)
  have hηF : (fun w i => coefficients (r := r) E v a w (fun _ => i)) = fun w i => η w • F w i := by
    funext w i
    ext α
    exact coefficients_multiplyForm E (fun x => (χ x : ℂ)) U.1 a w (fun _ => i) α
  rw [hηF, chartDbarAdjoint_mul_scalar_local E g h hh φ hφ a η F
    (fun i α => hU a (fun _ => i) α) z hz hη, ← hSF] at hRF
  have hC : WithLp.toLp 2 (fun α => ∑ i, wirt η z (stdVec i) * chartOneRaise g.form a F z i α) =
      chartScalarContraction (r := r) E g.form χ U.1 a z := by
    ext α
    simp only [chartScalarContraction, chartScalarWirt, raisedOneCoefficientsMatrix,
      Matrix.vecMul, dotProduct, chartOneRaise, oneCoefficientsMatrix, Matrix.mul_apply,
      F, η]
  ext α
  rw [hRF, coefficients_sub, coefficients_multiplyForm,
    coefficients_scalarGradientContraction E g.form χ hχ U.1 a z hz, hC]
  rfl

end Yau.LeafProofs.L14Aux
