import Yau.Proofs.F03DirichletRieszKernel

/-! Actual L² source representation by the single constructed Riesz kernel. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- The actual kernel product is globally integrable for every genuine
restricted-L² source, with no condition on its exterior representative. -/
theorem dirichletKernelCandidate_source_integrable (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) (hx : x ∈ Ω) (f : M.Carrier → ℝ) (hf : ScalarL2 (μ.restrict Ω) f) :
    Integrable (fun y => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y) μ := by
  have hi : Integrable (fun y => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y)
      (μ.restrict Ω) :=
    ((scalarL2_iff_memLp _ _).mp (dirichletKernelCandidate_row_scalarL2 g hK μ hμ Ω hΩ ht x hx)).integrable_mul
      ((scalarL2_iff_memLp _ _).mp hf)
  have hiInd : Integrable (Ω.indicator (fun y => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y)) μ :=
    (integrable_indicator_iff hΩ.measurableSet).mpr hi
  have heq : Ω.indicator (fun y => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y) =
      (fun y => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y) := by
    funext y
    by_cases hy : y ∈ Ω
    · exact Set.indicator_of_mem hy _
    · rw [Set.indicator_of_notMem hy,dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inr hy),zero_mul]
  rwa [heq] at hiInd

/-- The actual integral against the one kernel equals the actual classical
supported heat for every source at every positive interior point. -/
theorem dirichletKernelCandidate_evolution_inside (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) (hx : x ∈ Ω) (f : M.Carrier → ℝ) (hf : ScalarL2 (μ.restrict Ω) f) :
    boundedKernelEvolution μ (dirichletKernelCandidate g hK μ hμ Ω hΩ) f t x =
      dirichletClassicalHeat g hK μ hμ Ω hΩ (scalarToLp hf) x t := by
  rw [boundedKernelEvolution,if_neg ht.ne']
  have hr : (∫ y in Ω, dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y ∂μ) =
      ∫ y, dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inr hy),zero_mul]
  rw [← hr]
  have hi : (∫ y in Ω, dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y ∂μ) =
      inner ℝ (dirichletHeatEvaluationVector g hK μ hμ Ω hΩ x hx t ht) (scalarToLp hf) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletKernelCandidate_row_ae g hK μ hμ Ω hΩ ht x hx,
      scalarToLp_coe hf] with y hy hfy
    simp only [hy,hfy,RCLike.inner_apply,conj_trivial,mul_comm]
  rw [hi,dirichletHeatEvaluationVector_inner]

theorem dirichletKernelCandidate_evolution_outside (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (x : M.Carrier) (hx : x ∉ Ω) (f : M.Carrier → ℝ) :
    boundedKernelEvolution μ (dirichletKernelCandidate g hK μ hμ Ω hΩ) f t x = 0 := by
  rw [boundedKernelEvolution,if_neg ht.ne']
  have heq : (fun y => dirichletKernelCandidate g hK μ hμ Ω hΩ t x y * f y) = fun _ => (0 : ℝ) := by
    funext y
    rw [dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inl hx),zero_mul]
  rw [heq,integral_zero]

/-- The exact integral source evolution is the same zero-outside classical
heat function, for all representatives of genuine L² data. -/
theorem dirichletKernelCandidate_evolution_eq (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (f : M.Carrier → ℝ) (hf : ScalarL2 (μ.restrict Ω) f) :
    boundedKernelEvolution μ (dirichletKernelCandidate g hK μ hμ Ω hΩ) f t =
      fun x => dirichletClassicalHeat g hK μ hμ Ω hΩ (scalarToLp hf) x t := by
  funext x
  by_cases hx : x ∈ Ω
  · exact dirichletKernelCandidate_evolution_inside g hK μ hμ Ω hΩ ht x hx f hf
  · rw [dirichletKernelCandidate_evolution_outside g hK μ hμ Ω hΩ ht x hx f,
      dirichletClassicalHeat_zero_outside g hK μ hμ Ω hΩ _ x hx]

theorem dirichletKernelCandidate_evolution_ae (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (f : M.Carrier → ℝ) (hf : ScalarL2 (μ.restrict Ω) f) :
    boundedKernelEvolution μ (dirichletKernelCandidate g hK μ hμ Ω hΩ) f t =ᵐ[μ.restrict Ω]
      (dirichletHeat g μ hμ Ω t (scalarToLp hf) : M.Carrier → ℝ) := by
  rw [dirichletKernelCandidate_evolution_eq g hK μ hμ Ω hΩ ht f hf]
  exact dirichletClassicalHeat_ae g hK μ hμ Ω hΩ (scalarToLp hf) ht

theorem dirichletKernelCandidate_evolution_scalarL2 (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t)
    (f : M.Carrier → ℝ) (hf : ScalarL2 (μ.restrict Ω) f) :
    ScalarL2 (μ.restrict Ω)
      (boundedKernelEvolution μ (dirichletKernelCandidate g hK μ hμ Ω hΩ) f t) := by
  apply (scalarL2_iff_memLp _ _).mpr
  exact MemLp.ae_eq (dirichletKernelCandidate_evolution_ae g hK μ hμ Ω hΩ ht f hf).symm (Lp.memLp _)

end Yau.Proofs.F03Aux
