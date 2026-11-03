import Yau.Proofs.F03ExhaustionKernelFamily

/-! The finite pointwise increasing limit of the actual exhaustion kernels. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

def dirichletMinimalKernelCandidate (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O)
    (t : ℝ) (x y : M.Carrier) : ℝ :=
  ⨆ j, dirichletExhaustionKernels g hK μ hμ O hO j t x y

theorem dirichletExhaustionKernels_le_limit (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) (j : ℕ) :
    dirichletExhaustionKernels g hK μ hμ O hO j t x y ≤
      dirichletMinimalKernelCandidate g hK μ hμ O hO t x y :=
  le_ciSup (dirichletExhaustionKernels_bddAbove g hK μ hμ O hO ht x y) j

theorem dirichletExhaustionKernels_tendsto (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) :
    Tendsto (fun j => dirichletExhaustionKernels g hK μ hμ O hO j t x y) atTop
      (𝓝 (dirichletMinimalKernelCandidate g hK μ hμ O hO t x y)) :=
  tendsto_atTop_ciSup (dirichletExhaustionKernels_monotone g hK μ hμ O hO ht x y)
    (dirichletExhaustionKernels_bddAbove g hK μ hμ O hO ht x y)

theorem dirichletMinimalKernelCandidate_le_univ (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) :
    dirichletMinimalKernelCandidate g hK μ hμ O hO t x y ≤
      dirichletKernelCandidate g hK μ hμ Set.univ isOpen_univ t x y :=
  ciSup_le (dirichletExhaustionKernels_le_univ g hK μ hμ O hO ht x y)

theorem dirichletMinimalKernelCandidate_nonneg (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) : 0 ≤ dirichletMinimalKernelCandidate g hK μ hμ O hO t x y :=
  (dirichletKernelCandidate_nonneg g hK μ hμ (O 0) (hO.1 0).1 ht x y).trans
    (dirichletExhaustionKernels_le_limit g hK μ hμ O hO ht x y 0)

theorem dirichletMinimalKernelCandidate_symm (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) :
    dirichletMinimalKernelCandidate g hK μ hμ O hO t x y =
      dirichletMinimalKernelCandidate g hK μ hμ O hO t y x := by
  apply congrArg sSup
  apply congrArg Set.range
  funext j
  exact dirichletKernelCandidate_symm g hK μ hμ (O j) (hO.1 j).1 ht x y

theorem dirichletMinimalKernelCandidate_strict_pos (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : ℕ → Set M.Carrier) (hO : SmoothExhaustion O) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) : 0 < dirichletMinimalKernelCandidate g hK μ hμ O hO t x y := by
  have hc := smoothExhaustion_eventually_contains_compact hO
    ((isCompact_singleton : IsCompact ({x} : Set M.Carrier)).union
      (isCompact_singleton : IsCompact ({y} : Set M.Carrier)))
  obtain ⟨j,hj⟩ := hc.exists
  have hx : x ∈ O j := hj (by simp)
  have hy : y ∈ O j := hj (by simp)
  exact (dirichletKernelCandidate_strict_pos g hK μ hμ (O j) (hO.1 j).1
    (hO.1 j).2.2.1.2 x y hx hy ht).trans_le
      (dirichletExhaustionKernels_le_limit g hK μ hμ O hO ht x y j)

end Yau.Proofs.F03Aux
