import Yau.Proofs.F03DirichletEvaluation
import Yau.Proofs.F03LpPositiveCone

/-! One genuine Riesz kernel chosen before every source, with actual heat rows. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletHeatEvaluationVector_nonneg (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (x : M.Carrier) (hx : x ∈ Ω)
    (t : ℝ) (ht : 0 < t) :
    ∀ᵐ y ∂μ.restrict Ω, 0 ≤ dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht y := by
  apply lp_nonneg_of_inner_nonneg
  intro f hf
  rw [dirichletHeatEvaluationVector_inner]
  exact dirichletClassicalHeat_nonneg g hK μ hμ Ω hΩ f hf ht x hx

/-- This single kernel depends only on the actual geometry, volume and
open domain, before every source. The remaining kernel clauses are proved
in subsequent construction cards. -/
def dirichletKernelCandidate (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (t : ℝ) (x y : M.Carrier) : ℝ := by
  classical
  exact if ht : 0 < t then if hx : x ∈ Ω then if hy : y ∈ Ω then
    inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht))
      (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy (t/2) (half_pos ht))
  else 0 else 0 else 0

theorem dirichletKernelCandidate_of_members (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ t x y =
      inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht))
        (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy (t/2) (half_pos ht)) := by
  simp only [dirichletKernelCandidate,dite_eq_left ht,dite_eq_left hx,dite_eq_left hy]

theorem dirichletKernelCandidate_zero_off (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x y : M.Carrier) (hxy : x ∉ Ω ∨ y ∉ Ω) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ t x y = 0 := by
  rcases hxy with hx | hy
  · simp [dirichletKernelCandidate,ht,hx]
  · by_cases hx : x ∈ Ω <;> simp [dirichletKernelCandidate,ht,hx,hy]

theorem dirichletKernelCandidate_symm (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t) (x y : M.Carrier) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ t x y =
      dirichletKernelCandidate g hK μ hμ Ω hΩ t y x := by
  by_cases hx : x ∈ Ω <;> by_cases hy : y ∈ Ω <;>
    simp [dirichletKernelCandidate,ht,hx,hy,real_inner_comm]

theorem dirichletKernelCandidate_nonneg (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t) (x y : M.Carrier) :
    0 ≤ dirichletKernelCandidate g hK μ hμ Ω hΩ t x y := by
  by_cases hx : x ∈ Ω
  · by_cases hy : y ∈ Ω
    · rw [dirichletKernelCandidate_of_members g hK μ hμ Ω hΩ ht x y hx hy]
      exact lp_inner_nonneg_of_ae_nonneg _ _ _
        (dirichletHeatEvaluationVector_nonneg g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht))
        (dirichletHeatEvaluationVector_nonneg g hK μ hμ Ω hΩ y hy (t/2) (half_pos ht))
    · rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inr hy)]
  · rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inl hx)]

/-- Each row of the fixed kernel is the actual classical supported heat
of its fixed half-time Riesz vector, including every exterior point. -/
theorem dirichletKernelCandidate_row_classical (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) (hx : x ∈ Ω) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ t x = fun y =>
      dirichletClassicalHeat g hK μ hμ Ω hΩ
        (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht)) y (t/2) := by
  funext y
  by_cases hy : y ∈ Ω
  · rw [dirichletKernelCandidate_of_members g hK μ hμ Ω hΩ ht x y hx hy,
      ← dirichletHeatEvaluationVector_inner g hK μ hμ Ω hΩ y hy (t/2) (half_pos ht)]
    exact real_inner_comm _ _
  · rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inr hy),
      dirichletClassicalHeat_zero_outside g hK μ hμ Ω hΩ _ y hy]

/-- A row represents the actual full-time evaluation vector in the
original restricted L² space. -/
theorem dirichletKernelCandidate_row_ae (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) (hx : x ∈ Ω) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ t x =ᵐ[μ.restrict Ω]
      (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht : M.Carrier → ℝ) := by
  rw [dirichletKernelCandidate_row_classical g hK μ hμ Ω hΩ ht x hx]
  have hv := dirichletHeatEvaluationVector_semigroup g hK μ hμ Ω hΩ x hx
    (half_pos ht) (half_pos ht).le
  have hsum : t/2+t/2 = t := by ring
  have hv' : dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht =
      dirichletHeat g μ hμ Ω (t/2)
        (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t/2) (half_pos ht)) := by
    simpa only [hsum] using hv
  rw [hv']
  exact dirichletClassicalHeat_ae g hK μ hμ Ω hΩ _ (half_pos ht)

theorem dirichletKernelCandidate_row_scalarL2 (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) (hx : x ∈ Ω) :
    ScalarL2 (μ.restrict Ω) (dirichletKernelCandidate g hK μ hμ Ω hΩ t x) := by
  apply (scalarL2_iff_memLp _ _).mpr
  exact MemLp.ae_eq (dirichletKernelCandidate_row_ae g hK μ hμ Ω hΩ ht x hx).symm
    (Lp.memLp (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht))

end Yau.Proofs.F03Aux
