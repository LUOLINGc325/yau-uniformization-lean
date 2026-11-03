import Yau.Proofs.F03DirichletRieszKernel

/-! Actual time splits of the single Riesz kernel and fixed-source heat germs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem dirichletKernelCandidate_split_of_le (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) (x y : M.Carrier) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ (a+b) x y =
      inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx a ha)
        (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy b hb) := by
  let δ := (a+b)/2
  have hδ : 0 < δ := half_pos (add_pos ha hb)
  let r := δ-a
  have hr : 0 ≤ r := by dsimp [r,δ]; linarith
  have hxa : a+r = δ := by dsimp [r]; ring
  have hyb : δ+r = b := by dsimp [r,δ]; ring
  have hxδ : dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx δ hδ =
      dirichletHeat g μ hμ Ω r (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx a ha) := by
    simpa only [hxa] using dirichletHeatEvaluationVector_semigroup g hK μ hμ Ω hΩ x hx ha hr
  have hybVec : dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy b hb =
      dirichletHeat g μ hμ Ω r (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy δ hδ) := by
    simpa only [hyb] using dirichletHeatEvaluationVector_semigroup g hK μ hμ Ω hΩ y hy hδ hr
  rw [dirichletKernelCandidate_of_members g hK μ hμ Ω hΩ (add_pos ha hb) x y hx hy]
  change inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx δ hδ)
    (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy δ hδ) = _
  rw [hxδ,hybVec]
  simpa only [dirichletHeat_adjoint] using
    (ContinuousLinearMap.adjoint_inner_right (dirichletHeat g μ hμ Ω r)
      (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx a ha)
      (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy δ hδ)).symm

/-- Any two positive times give the SAME kernel through their actual
Riesz-vector pairing. This derives from the single heat semigroup. -/
theorem dirichletKernelCandidate_split (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : M.Carrier) (hx : x ∈ Ω) (hy : y ∈ Ω) :
    dirichletKernelCandidate g hK μ hμ Ω hΩ (a+b) x y =
      inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx a ha)
        (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy b hb) := by
  rcases le_total a b with hab | hba
  · exact dirichletKernelCandidate_split_of_le g hK μ hμ Ω hΩ ha hb hab x y hx hy
  · calc
      _ = dirichletKernelCandidate g hK μ hμ Ω hΩ (b+a) x y :=
        congrArg (fun t => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y) (add_comm a b)
      _ = dirichletKernelCandidate g hK μ hμ Ω hΩ (b+a) y x :=
        dirichletKernelCandidate_symm g hK μ hμ Ω hΩ (add_pos hb ha) x y
      _ = inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy b hb)
          (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx a ha) :=
        dirichletKernelCandidate_split_of_le g hK μ hμ Ω hΩ hb ha hba y x hy hx
      _ = _ := real_inner_comm _ _

/-- With one positive time fixed, the actual kernel is the classical heat
of one fixed source throughout the remaining positive-time interval. -/
theorem dirichletKernelCandidate_split_heat (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t b : ℝ} (hb : 0 < b) (hbt : b < t)
    (y : M.Carrier) (hy : y ∈ Ω) :
    (fun x => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y) =
      fun x => dirichletClassicalHeat g hK μ hμ Ω hΩ
        (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy b hb) x (t-b) := by
  funext x
  by_cases hx : x ∈ Ω
  · have hs := dirichletKernelCandidate_split g hK μ hμ Ω hΩ (sub_pos.mpr hbt) hb x y hx hy
    have hsum : (t-b)+b = t := by ring
    have hs' : dirichletKernelCandidate g hK μ hμ Ω hΩ t x y =
        inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx (t-b) (sub_pos.mpr hbt))
          (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ y hy b hb) := by
      simpa only [hsum] using hs
    rw [hs',dirichletHeatEvaluationVector_inner]
  · rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ (hb.trans hbt) x y (Or.inl hx),
      dirichletClassicalHeat_zero_outside g hK μ hμ Ω hΩ _ x hx]

end Yau.Proofs.F03Aux
