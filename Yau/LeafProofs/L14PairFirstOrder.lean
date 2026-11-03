import Yau.LeafProofs.L14TwoAdjointModel
import Yau.LeafProofs.L14DivergenceSystem

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle Filter Module

namespace Yau.LeafProofs.L14Aux
open BundleDbar

def wirtBarRealCoefficient (t : Fin 2) : ℂ :=
  if t = 0 then 1 / 2 else Complex.I / 2

theorem wirtBar_eq_real_directions {n : ℕ} (f : ComplexVector n → ℂ)
    (z : ComplexVector n) (i : Fin n) :
    wirtBar f z (stdVec i) =
      wirtBarRealCoefficient 0 * fderiv ℝ f z (realVec (i, 0)) +
      wirtBarRealCoefficient 1 * fderiv ℝ f z (realVec (i, 1)) := by
  simp only [wirtBar, wirtBarRealCoefficient, realVec, stdVec, ite_true, one_smul]
  norm_num
  ring

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- The actual top-form coefficients and the full ordered two-form coefficients. -/
abbrev PairSystemInputIndex (n r : ℕ) := Sum (Fin r) (TwoCoefficientIndex n r)

/-- The weighted one-dual of the principal symbol of `modelTopDbar`. -/
def topDualFirstOrderDerivative (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (β : Fin r) (d : RIdx n) (z : ComplexVector n) : ℂ :=
  (Real.exp (-φ (chartInv a z)) : ℂ) *
    chartOneMetricMatrix (r := r) E g h a z row (d.1, β) * wirtBarRealCoefficient d.2

/-- The full ordered two-metric rows whose divergence is the one-dual of the adjoint. -/
def twoDualDivergenceCoefficient (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (p : TwoCoefficientIndex n r) (i : Fin n) (z : ComplexVector n) : ℂ :=
  (Real.exp (-φ (chartInv a z)) : ℂ) *
    chartTwoMetricMatrix (r := r) E g h a z ((row.2, i), row.1) p

def pairFirstOrderDerivative (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (c : PairSystemInputIndex n r) (d : RIdx n) (z : ComplexVector n) : ℂ :=
  match c with
  | .inl β => topDualFirstOrderDerivative (r := r) E g h φ a row β d z
  | .inr p => wirtDivergenceDerivative (twoDualDivergenceCoefficient (r := r) E g h φ a) row p d z

def pairFirstOrderValue (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (row : Fin n × Fin r)
    (c : PairSystemInputIndex n r) (z : ComplexVector n) : ℂ :=
  match c with
  | .inl _ => 0
  | .inr p => wirtDivergenceValue (twoDualDivergenceCoefficient (r := r) E g h φ a) row p z

def pairSystemInput (A : ComplexVector n → ComplexVector r)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (z : ComplexVector n) (c : PairSystemInputIndex n r) : ℂ :=
  match c with
  | .inl β => A z β
  | .inr p => F z p.1.2 p.2 p.1.1

theorem twoDualDivergenceCoefficient_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (p : TwoCoefficientIndex n r) (i : Fin n) :
    ContDiffOn ℝ ∞ (twoDualDivergenceCoefficient (r := r) E g.form h φ a row p i)
      (localDomain (r := r) E a) := by
  have he : ContDiffOn ℝ ∞ (fun z => (Real.exp (-φ (chartInv a z)) : ℂ))
      (localDomain (r := r) E a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn (((hφ a).mono Set.inter_subset_left).neg))
  exact he.mul (chartTwoMetricMatrix_contDiffOn E g h hh a ((row.2,i),row.1) p)

theorem topDualFirstOrderDerivative_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (β : Fin r) (d : RIdx n) :
    ContDiffOn ℝ ∞ (topDualFirstOrderDerivative (r := r) E g.form h φ a row β d)
      (localDomain (r := r) E a) := by
  have he : ContDiffOn ℝ ∞ (fun z => (Real.exp (-φ (chartInv a z)) : ℂ))
      (localDomain (r := r) E a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (Real.contDiff_exp.comp_contDiffOn (((hφ a).mono Set.inter_subset_left).neg))
  exact (he.mul (chartOneMetricMatrix_contDiffOn E g h hh a row (d.1,β))).mul contDiffOn_const

theorem pairFirstOrderDerivative_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (c : PairSystemInputIndex n r) (d : RIdx n) :
    ContDiffOn ℝ ∞ (pairFirstOrderDerivative (r := r) E g.form h φ a row c d)
      (localDomain (r := r) E a) := by
  cases c with
  | inl β => exact topDualFirstOrderDerivative_contDiffOn E g h hh φ hφ a row β d
  | inr p =>
    exact contDiffOn_const.mul (twoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row p d.1)

theorem pairFirstOrderValue_contDiffOn (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (row : Fin n × Fin r) (c : PairSystemInputIndex n r) :
    ContDiffOn ℝ ∞ (pairFirstOrderValue (r := r) E g.form h φ a row c)
      (localDomain (r := r) E a) := by
  cases c with
  | inl β => exact contDiffOn_const
  | inr p =>
    apply ContDiffOn.neg
    apply ContDiffOn.sum
    intro i _
    exact wirt_contDiffOn (localDomain_isOpen E a) _
      (twoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row p i) (stdVec i)

theorem topDualFirstOrder_apply (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (a : M.Carrier) (A : ComplexVector n → ComplexVector r)
    (z : ComplexVector n) (row : Fin n × Fin r) :
    complexFirstOrderSystemApply realVec (topDualFirstOrderDerivative (r := r) E g h φ a)
      (fun _ _ _ => 0) (fun w β => A w β) z row =
    chartOneDual (r := r) E g h φ a (modelTopDbar A) z row.1 row.2 := by
  classical
  have hprincipal (β : Fin r) :
      (∑ d : RIdx n, topDualFirstOrderDerivative (r := r) E g h φ a row β d z *
        fderiv ℝ (fun w => A w β) z (realVec d)) =
      ∑ k : Fin n, (Real.exp (-φ (chartInv a z)) : ℂ) *
        chartOneMetricMatrix (r := r) E g h a z row (k,β) *
          wirtBar (fun w => A w β) z (stdVec k) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.sum_univ_two, topDualFirstOrderDerivative, wirtBar_eq_real_directions]
    ring
  simp only [complexFirstOrderSystemApply, zero_mul, add_zero, hprincipal,
    chartOneDual_eq_weighted_matrix, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    modelTopDbar]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

theorem twoDualFirstOrder_apply (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (F : ComplexVector n → Fin n → Fin n → ComplexVector r)
    (hF : ContDiff ℝ ∞ F) (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a)
    (row : Fin n × Fin r) :
    complexFirstOrderSystemApply realVec
      (wirtDivergenceDerivative (twoDualDivergenceCoefficient (r := r) E g.form h φ a))
      (wirtDivergenceValue (twoDualDivergenceCoefficient (r := r) E g.form h φ a))
      (fun w p => F w p.1.2 p.2 p.1.1) z row =
    chartOneDual (r := r) E g.form h φ a (chartTwoDbarAdjoint E g.form h φ a F) z row.1 row.2 := by
  have hC (p : TwoCoefficientIndex n r) (i : Fin n) : DifferentiableAt ℝ
      (twoDualDivergenceCoefficient (r := r) E g.form h φ a row p i) z :=
    ((twoDualDivergenceCoefficient_contDiffOn E g h hh φ hφ a row p i).contDiffAt
      ((localDomain_isOpen E a).mem_nhds hz)).differentiableAt (by simp)
  have hFc (p : TwoCoefficientIndex n r) : DifferentiableAt ℝ
      (fun w => F w p.1.2 p.2 p.1.1) z :=
    ((contDiff_piLp 2).mp ((contDiff_pi.mp ((contDiff_pi.mp hF) p.1.2)) p.2) p.1.1).differentiable (by simp) z
  rw [wirtDivergence_system_apply _ _ z row hC hFc,
    chartTwoDbarAdjoint_dual E g.form h φ a F z hz row.1 row.2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext w
  simp only [twoDualDivergenceCoefficient, chartTwoDual, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc]

/-- The finite first-order system for `dbar A + delta₂ F`, in actual weighted one-dual coordinates.
No antisymmetry is needed for this coefficient identity. -/
theorem pairFirstOrder_apply (g : Yau.SmoothMetric M) (h : Metric E)
    (hh : BundleDbar.SmoothMetric (r := r) E h) (φ : M.Carrier → ℝ) (hφ : SmoothFn φ)
    (a : M.Carrier) (A : ComplexVector n → ComplexVector r)
    (F : ComplexVector n → Fin n → Fin n → ComplexVector r) (hF : ContDiff ℝ ∞ F)
    (z : ComplexVector n) (hz : z ∈ localDomain (r := r) E a) (row : Fin n × Fin r) :
    complexFirstOrderSystemApply realVec (pairFirstOrderDerivative (r := r) E g.form h φ a)
      (pairFirstOrderValue (r := r) E g.form h φ a) (pairSystemInput A F) z row =
    chartOneDual (r := r) E g.form h φ a (modelTopDbar A) z row.1 row.2 +
      chartOneDual (r := r) E g.form h φ a (chartTwoDbarAdjoint E g.form h φ a F) z row.1 row.2 := by
  change (∑ c : PairSystemInputIndex n r, _) = _
  rw [Fintype.sum_sum_type]
  exact congrArg₂ (· + ·) (topDualFirstOrder_apply E g.form h φ a A z row)
    (twoDualFirstOrder_apply E g h hh φ hφ a F hF z hz row)

end Yau.LeafProofs.L14Aux
