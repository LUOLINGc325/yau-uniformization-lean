import Yau.LeafProofs.L03DiracLocalizedFields

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- Compact actual scalar chart multipliers also give honest L¹ scalar
coordinates, as required for splitting the weak distribution integrals. -/
theorem modelGradedChartPullbackZero_cutoff_coord_integrable {α : Type*} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : OperatorCandidates.GradedRealForm M) (hA : OperatorCandidates.GradedL2 g.form μ A)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) (c : α) :
    Integrable (fun z => φ z * b.repr (modelGradedChartPullbackZero A x z) c) (lebesgueC n) := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  exact memLp_two_compact_integrable (lebesgueC n) _
    (modelGradedChartPullbackZero_cutoff_coord_memLp g μ hμ A hA x b φ hφ hcφ hφO c) hcφ.mul_right

set_option maxHeartbeats 1500000 in
/-- The original actual maximal graph localizes to the precise scalar row
for the compact input and its explicitly constructed local output. No raw
form is differentiated, and the commutator has the positive product-rule sign. -/
theorem diracMaximalGraph_localized_chart_row_test {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A W : OperatorCandidates.GradedRealForm M)
    (hmax : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (x : M.Carrier) (b : Basis α ℝ (modelGradedFiber n))
    (φ : ComplexVector n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ chartTarget x) (r : α)
    (ψ : ComplexVector n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (∫ z, ψ z * diracLocalizedChartScalarOutput g.form x b φ A W z r ∂lebesgueC n) =
      ∫ z, ∑ c, (φ z * b.repr (modelGradedChartPullbackZero A x z) c) *
        diracFormalAdjointTestRow g.form x b r c ψ z ∂lebesgueC n := by
  classical
  let u := fun z c => b.repr (modelGradedChartPullbackZero A x z) c
  let w := fun z => b.repr (modelGradedChartPullbackZero W x z) r
  let a := diracScalarDerivativeCoefficient g.form x b r
  let T := fun c z => (φ z * u z c) * diracFormalAdjointTestRow g.form x b r c ψ z
  let S := fun c i z => ψ z * (a c i z * fderiv ℝ φ z (realModelBasis n i) * u z c)
  let V := fun z => ψ z * (φ z * w z)
  have hT (c : α) : Integrable (T c) (lebesgueC n) := by
    have hp := scalar_cutoff_contDiff_properties (isOpen_extChartAt_target (I := ComplexModel n) x)
      φ hφ hcφ hφO (diracFormalAdjointTestRow g.form x b r c ψ)
      (diracFormalAdjointTestRow_contDiffOn g x b r c ψ hψ)
    have hi := modelGradedChartPullbackZero_cutoff_coord_integrable g μ hμ A hmax.1 x b _ hp.1 hp.2.1
      (hp.2.2.trans hφO) c
    apply hi.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [T, u]; ring
  have hS (c : α) (i : RIdx n) : Integrable (S c i) (lebesgueC n) := by
    have hd := diracScalar_cutoff_derivative_properties g x b φ hφ hcφ hφO r c i
    have hf : ContDiff ℝ ∞ (fun z => ψ z * (a c i z * fderiv ℝ φ z (realModelBasis n i))) := hψ.mul hd.1
    have hcf : HasCompactSupport (fun z => ψ z * (a c i z * fderiv ℝ φ z (realModelBasis n i))) := hd.2.1.mul_left
    have hfo : tsupport (fun z => ψ z * (a c i z * fderiv ℝ φ z (realModelBasis n i))) ⊆ chartTarget x :=
      tsupport_mul_subset_right.trans (hd.2.2.trans hφO)
    have hi := modelGradedChartPullbackZero_cutoff_coord_integrable g μ hμ A hmax.1 x b _ hf hcf hfo c
    apply hi.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [S, u]; ring
  have hV : Integrable V (lebesgueC n) := by
    have hi := modelGradedChartPullbackZero_cutoff_coord_integrable g μ hμ W hmax.2.1 x b
      (fun z => ψ z * φ z) (hψ.mul hφ) hcφ.mul_left (tsupport_mul_subset_right.trans hφO) r
    apply hi.congr
    exact Filter.Eventually.of_forall fun z => by dsimp only [V, w]; ring
  have hSi (c : α) : Integrable (fun z => ∑ i, S c i z) (lebesgueC n) :=
    integrable_finsetSum Finset.univ (fun i _ => hS c i)
  have hSs : Integrable (fun z => ∑ c, ∑ i, S c i z) (lebesgueC n) :=
    integrable_finsetSum Finset.univ (fun c _ => hSi c)
  have hTs : Integrable (fun z => ∑ c, T c z) (lebesgueC n) :=
    integrable_finsetSum Finset.univ (fun c _ => hT c)
  have hrow (c : α) (z : ComplexVector n) : u z c *
      diracFormalAdjointTestRow g.form x b r c (fun y => φ y * ψ y) z =
      T c z - ∑ i, S c i z := by
    rw [diracFormalAdjointTestRow_mul g.form x b r c φ ψ
      (hφ.differentiable (by simp)) (hψ.differentiable (by simp))]
    have hs : (∑ i, S c i z) = (u z c * ψ z) * ∑ i, a c i z * fderiv ℝ φ z (realModelBasis n i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [S]
      ring
    rw [hs]
    dsimp only [T, a]
    ring
  have hRi (c : α) : Integrable (fun z => u z c *
      diracFormalAdjointTestRow g.form x b r c (fun y => φ y * ψ y) z) (lebesgueC n) := by
    have he : (fun z => u z c * diracFormalAdjointTestRow g.form x b r c (fun y => φ y * ψ y) z) =
        (fun z => T c z - ∑ i, S c i z) := funext (hrow c)
    rw [he]
    exact (hT c).sub (hSi c)
  have hRint (c : α) : (∫ z, u z c * diracFormalAdjointTestRow g.form x b r c
      (fun y => φ y * ψ y) z ∂lebesgueC n) =
      (∫ z, T c z ∂lebesgueC n) - ∑ i, ∫ z, S c i z ∂lebesgueC n := by
    rw [show (fun z => u z c * diracFormalAdjointTestRow g.form x b r c (fun y => φ y * ψ y) z) =
      (fun z => T c z - ∑ i, S c i z) from funext (hrow c),
      integral_sub (hT c) (hSi c), integral_finsetSum Finset.univ (fun i _ => hS c i)]
  have hagg := diracMaximalGraph_zeroPullback_scalar_test g μ hμ A W hmax x b r
    (fun z => φ z * ψ z) (hφ.mul hψ) hcφ.mul_right (tsupport_mul_subset_left.trans hφO)
  change (∫ z, (φ z * ψ z) * w z ∂lebesgueC n) =
    ∫ z, ∑ c, u z c * diracFormalAdjointTestRow g.form x b r c (fun y => φ y * ψ y) z ∂lebesgueC n at hagg
  have hleft : (∫ z, (φ z * ψ z) * w z ∂lebesgueC n) = ∫ z, V z ∂lebesgueC n :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by dsimp only [V]; ring)
  rw [hleft, integral_finsetSum Finset.univ (fun c _ => hRi c)] at hagg
  simp_rw [hRint] at hagg
  rw [Finset.sum_sub_distrib] at hagg
  have hout : (fun z => ψ z * diracLocalizedChartScalarOutput g.form x b φ A W z r) =
      (fun z => V z + ∑ c, ∑ i, S c i z) := by
    funext z
    simp only [diracLocalizedChartScalarOutput, V, S, a, u, w, mul_add, Finset.mul_sum]
  rw [hout, integral_add hV hSs, integral_finsetSum Finset.univ (fun c _ => hSi c)]
  simp_rw [integral_finsetSum Finset.univ (fun i _ => hS _ i)]
  change (∫ z, V z ∂lebesgueC n) + (∑ c, ∑ i, ∫ z, S c i z ∂lebesgueC n) =
    ∫ z, ∑ c, T c z ∂lebesgueC n
  rw [integral_finsetSum Finset.univ (fun c _ => hT c)]
  linarith

end Yau.LeafProofs.L03
