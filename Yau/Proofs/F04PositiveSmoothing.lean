import Yau.Proofs.F04SmoothCompositionGraph
import Yau.Proofs.F04SmoothPositiveL2
import Yau.Proofs.F04PositiveIndicator

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Proofs.F03Aux Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

theorem smoothPositive_deriv_abs_le (δ s : ℝ) : |deriv (smoothPositive δ) s| ≤ 1 := by
  have hd := smoothPositive_deriv_bounds δ s
  rw [abs_of_nonneg hd.1]
  exact hd.2

def dirichletPositiveSmoothing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (δ : ℝ) (u : DirichletEnergy g μ hμ O) : DirichletEnergy g μ hμ O :=
  dirichletSmoothComp g μ hμ O (smoothPositive δ) (smoothPositive_contDiff δ)
    (smoothPositive_zero δ) 1 zero_le_one (smoothPositive_deriv_abs_le δ) u

theorem dirichletPositiveSmoothing_L2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (δ : ℝ) (u : DirichletEnergy g μ hμ O) :
    dirichletL2 g μ hμ O (dirichletPositiveSmoothing g μ hμ O δ u) =
      smoothPositiveL2 (μ.restrict O) δ (dirichletL2 g μ hμ O u) := by
  rw [dirichletPositiveSmoothing, (dirichletSmoothComp_spec g μ hμ O (smoothPositive δ)
    (smoothPositive_contDiff δ) (smoothPositive_zero δ) 1 zero_le_one
    (smoothPositive_deriv_abs_le δ) u).1]
  apply Lp.ext
  filter_upwards [(smoothScalar_lipschitz (smoothPositive δ) (smoothPositive_contDiff δ)
      1 zero_le_one (smoothPositive_deriv_abs_le δ)).coeFn_compLp (smoothPositive_zero δ)
      (dirichletL2 g μ hμ O u),
    smoothPositiveL2_coe (μ.restrict O) δ (dirichletL2 g μ hμ O u)] with x hx hy
  exact hx.trans hy.symm

theorem dirichletPositiveSmoothing_D (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (δ : ℝ) (u : DirichletEnergy g μ hμ O) :
    dirichletD g μ hμ O (dirichletPositiveSmoothing g μ hμ O δ u) =
      continuousFormMultiplier g (μ.restrict O) (deriv (smoothPositive δ))
        (contDiff_infty_iff_deriv.mp (smoothPositive_contDiff δ)).2.continuous
        1 zero_le_one (smoothPositive_deriv_abs_le δ)
        (dirichletL2 g μ hμ O u) (dirichletD g μ hμ O u) :=
  (dirichletSmoothComp_spec g μ hμ O (smoothPositive δ) (smoothPositive_contDiff δ)
    (smoothPositive_zero δ) 1 zero_le_one (smoothPositive_deriv_abs_le δ) u).2

theorem positiveSmoothing_multiplier_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : Lp ℝ 2 μ) (a : L2FormHilbert g μ 1)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => continuousFormMultiplier g μ (deriv (smoothPositive (δ j)))
      (contDiff_infty_iff_deriv.mp (smoothPositive_contDiff (δ j))).2.continuous
      1 zero_le_one (smoothPositive_deriv_abs_le (δ j)) f a) atTop
      (𝓝 (positiveFormMultiplier g μ f a)) := by
  obtain ⟨A, hA, hrep⟩ := l2FormHilbert_exists_section g μ a
  rw [← hrep]
  apply bounded_form_multipliers_tendsto g μ A hA
    (fun j x => deriv (smoothPositive (δ j)) (f x)) (fun x => positiveIndicator (f x))
    (fun j => (contDiff_infty_iff_deriv.mp (smoothPositive_contDiff (δ j))).2.continuous
      |>.comp_aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable)
    (positiveIndicator_aestronglyMeasurable μ f) 1 zero_le_one
    (fun j x => smoothPositive_deriv_abs_le (δ j) (f x)) (fun x => positiveIndicator_abs_le (f x))
  apply ae_of_all
  intro x
  have ht := ((smoothPositive_deriv_tendsto (f x) δ hδ hlim).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => positiveIndicator (f x)) atTop
      (𝓝 (positiveIndicator (f x))))).pow 2
  simpa only [positiveIndicator, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_mul] using
    ht.mul_const (formNormSq g.form A x)

theorem dirichletPositiveSmoothing_D_tendsto
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (O : Set M.Carrier)
    (u : DirichletEnergy g μ hμ O) (δ : ℕ → ℝ)
    (hδ : ∀ j, 0 < δ j) (hlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun j => dirichletD g μ hμ O (dirichletPositiveSmoothing g μ hμ O (δ j) u))
      atTop (𝓝 (positiveFormMultiplier g (μ.restrict O)
        (dirichletL2 g μ hμ O u) (dirichletD g μ hμ O u))) := by
  simpa only [dirichletPositiveSmoothing_D] using
      positiveSmoothing_multiplier_tendsto g (μ.restrict O) (dirichletL2 g μ hμ O u)
        (dirichletD g μ hμ O u) δ hδ hlim

end Yau.F04Proof
