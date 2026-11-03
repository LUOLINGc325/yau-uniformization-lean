import Yau.LeafProofs.L03DiracLocalize

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- The exact local distributional output after multiplying a raw Dirac
input by a compact scalar chart cutoff. Only the cutoff is differentiated. -/
def diracLocalizedChartScalarOutput {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (A W : OperatorCandidates.GradedRealForm M) :
    ComplexVector n → α → ℝ := fun z r =>
  φ z * b.repr (modelGradedChartPullbackZero W x z) r +
    ∑ c, ∑ i : RIdx n, diracScalarDerivativeCoefficient g x b r c i z *
      fderiv ℝ φ z (realModelBasis n i) * b.repr (modelGradedChartPullbackZero A x z) c

def diracLocalizedChartOutput {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (A W : OperatorCandidates.GradedRealForm M) :
    ComplexVector n → modelGradedFiber n := fun z =>
  ∑ r, diracLocalizedChartScalarOutput g x b φ A W z r • b r

theorem diracLocalizedChartOutput_coordinates {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (A W : OperatorCandidates.GradedRealForm M)
    (z : ComplexVector n) (r : α) :
    b.repr (diracLocalizedChartOutput g x b φ A W z) r = diracLocalizedChartScalarOutput g x b φ A W z r :=
  congrFun (b.repr_sum_self (fun r => diracLocalizedChartScalarOutput g x b φ A W z r)) r

/-- Each actual local output coordinate is globally Euclidean L². Every
coefficient of a raw coordinate is itself a genuine compact smooth chart
multiplier, so unrestricted raw chart L² is never assumed. -/
theorem diracLocalizedChartScalarOutput_memLp {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hW : OperatorCandidates.GradedL2 g.form μ W)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) (r : α) :
    MemLp (fun z => diracLocalizedChartScalarOutput g.form x b φ A W z r) 2 (lebesgueC n) := by
  have hw := modelGradedChartPullbackZero_cutoff_coord_memLp g μ hμ W hW x b φ hφ hcφ hφO r
  have hcross (c : α) (i : RIdx n) : MemLp
      (fun z => diracScalarDerivativeCoefficient g.form x b r c i z *
        fderiv ℝ φ z (realModelBasis n i) * b.repr (modelGradedChartPullbackZero A x z) c) 2 (lebesgueC n) := by
    have hp := diracScalar_cutoff_derivative_properties g x b φ hφ hcφ hφO r c i
    exact modelGradedChartPullbackZero_cutoff_coord_memLp g μ hμ A hA x b _ hp.1 hp.2.1
      (hp.2.2.trans hφO) c
  have hc (c : α) : MemLp (fun z => ∑ i : RIdx n, diracScalarDerivativeCoefficient g.form x b r c i z *
      fderiv ℝ φ z (realModelBasis n i) * b.repr (modelGradedChartPullbackZero A x z) c) 2 (lebesgueC n) :=
    memLp_finsetSum Finset.univ (fun i _ => hcross c i)
  exact hw.add (memLp_finsetSum Finset.univ (fun c _ => hc c))

/-- The localized output vanishes off the scalar cutoff support. -/
theorem diracLocalizedChartOutput_zero_of_notMem_tsupport {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (A W : OperatorCandidates.GradedRealForm M)
    (z : ComplexVector n) (hz : z ∉ tsupport φ) : diracLocalizedChartOutput g x b φ A W z = 0 := by
  have hv (r : α) : diracLocalizedChartScalarOutput g x b φ A W z r = 0 := by
    simp only [diracLocalizedChartScalarOutput, image_eq_zero_of_notMem_tsupport hz,
      fderiv_of_notMem_tsupport (𝕜 := ℝ) hz, ContinuousLinearMap.zero_apply,
      zero_mul, mul_zero, Finset.sum_const_zero, zero_add]
  change (∑ r, diracLocalizedChartScalarOutput g x b φ A W z r • b r) = 0
  simp only [hv, zero_smul, Finset.sum_const_zero]

theorem diracLocalizedChartOutput_tsupport_subset {α : Type*} [Fintype α] [DecidableEq α]
    (g : HermitianField M) (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (A W : OperatorCandidates.GradedRealForm M) :
    tsupport (diracLocalizedChartOutput g x b φ A W) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro z hz
  by_contra hzφ
  exact hz (diracLocalizedChartOutput_zero_of_notMem_tsupport g x b φ A W z hzφ)

theorem diracLocalizedChartOutput_memLp {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hW : OperatorCandidates.GradedL2 g.form μ W)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    MemLp (diracLocalizedChartOutput g.form x b φ A W) 2 (lebesgueC n) := by
  have hsingle (r : α) : MemLp
      (fun z => diracLocalizedChartScalarOutput g.form x b φ A W z r • b r) 2 (lebesgueC n) :=
    (ContinuousLinearMap.toSpanSingleton ℝ (b r)).comp_memLp'
      (diracLocalizedChartScalarOutput_memLp g μ hμ A W hA hW x b φ hφ hcφ hφO r)
  have hm : MemLp (fun z => ∑ r : α, diracLocalizedChartScalarOutput g.form x b φ A W z r • b r)
      2 (lebesgueC n) :=
    memLp_finsetSum (f := fun r z => diracLocalizedChartScalarOutput g.form x b φ A W z r • b r)
      Finset.univ (fun r _ => hsingle r)
  exact hm

/-- The localized model output is an actual compact model L² field, with
support controlled by the scalar cutoff alone. -/
theorem diracLocalizedChartOutput_properties {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hA : OperatorCandidates.GradedL2 g.form μ A) (hW : OperatorCandidates.GradedL2 g.form μ W)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) :
    MemLp (diracLocalizedChartOutput g.form x b φ A W) 2 (lebesgueC n) ∧
      HasCompactSupport (diracLocalizedChartOutput g.form x b φ A W) ∧
      tsupport (diracLocalizedChartOutput g.form x b φ A W) ⊆ tsupport φ := by
  have hs := diracLocalizedChartOutput_tsupport_subset g.form x b φ A W
  exact ⟨diracLocalizedChartOutput_memLp g μ hμ A W hA hW x b φ hφ hcφ hφO,
    hcφ.of_isClosed_subset (isClosed_tsupport _) hs, hs⟩

/-- The localized model input pushes to exactly the original raw input
multiplied by the scalar chart pushforward, degree by degree. -/
theorem modelGradedChartPushforward_localized_input (x : M.Carrier) (φ : ComplexVector n → ℝ)
    (hφO : tsupport φ ⊆ chartTarget x) (A : OperatorCandidates.GradedRealForm M) :
    modelGradedChartPushforward x (fun z => φ z • modelGradedChartPullbackZero A x z) =
      fun j => multiplyRealForm (L18Aux.chartPushforwardZero x φ) (A j) := by
  funext j
  have he : (fun z => modelGradedProjection n j (φ z • modelGradedChartPullbackZero A x z)) =
      (fun z => φ z • chartForm (A j) x z) := by
    funext z
    by_cases hz : z ∈ chartTarget x
    · rw [map_smul, modelGradedChartPullbackZero_eq A x hz, modelGradedProjection_chart A x z j]
    · have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hφO h))
      rw [hφz, zero_smul, map_zero, zero_smul]
  change chartFormPushforward x (fun z => modelGradedProjection n j (φ z • modelGradedChartPullbackZero A x z)) = _
  rw [he, chartFormPushforward_scalar_chartForm]

end Yau.LeafProofs.L03
