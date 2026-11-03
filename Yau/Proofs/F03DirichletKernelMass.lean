import Yau.Proofs.F03DirichletKernelEvolution
import Yau.Proofs.F03DirichletClassicalBounds

/-! Actual integrable rows and sub-Markov mass of the one Dirichlet kernel. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem smoothPrecompactDomain_volume_lt_top (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω) : μ Ω < ⊤ := by
  have : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  exact lt_of_le_of_lt (measure_mono subset_closure) hΩ.2.2.2.1.measure_lt_top

/-- A genuine L² constant on a finite-volume domain and the actual Markov
property give the original row mass bound; no mass premise is supplied. -/
theorem dirichletKernelCandidate_mass_of_finite (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (hfin : μ Ω < ⊤)
    {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    Integrable (dirichletKernelCandidate g hK μ hμ Ω hΩ t x) μ ∧
      (∫ y, dirichletKernelCandidate g hK μ hμ Ω hΩ t x y ∂μ) ≤ 1 := by
  by_cases hx : x ∈ Ω
  · have : IsFiniteMeasure (μ.restrict Ω) := isFiniteMeasure_restrict.mpr hfin.ne
    have h1 : ScalarL2 (μ.restrict Ω) (fun _ : M.Carrier => (1 : ℝ)) :=
      (scalarL2_iff_memLp _ _).mpr (memLp_const 1)
    have hi : Integrable (dirichletKernelCandidate g hK μ hμ Ω hΩ t x) μ := by
      simpa only [mul_one] using
        dirichletKernelCandidate_source_integrable g hK μ hμ Ω hΩ ht x hx (fun _ => 1) h1
    have h1b : ∀ᵐ y ∂μ.restrict Ω, 0 ≤ scalarToLp h1 y ∧ scalarToLp h1 y ≤ 1 := by
      filter_upwards [scalarToLp_coe h1] with y hy
      rw [hy]
      exact ⟨zero_le_one,le_rfl⟩
    have hb := (dirichletClassicalHeat_submarkov g hK μ hμ Ω hΩ 1 zero_le_one
      (scalarToLp h1) h1b ht x hx).2
    have heq := dirichletKernelCandidate_evolution_inside g hK μ hμ Ω hΩ ht x hx (fun _ => 1) h1
    rw [boundedKernelEvolution,if_neg ht.ne'] at heq
    have heq' : (∫ y, dirichletKernelCandidate g hK μ hμ Ω hΩ t x y ∂μ) =
        dirichletClassicalHeat g hK μ hμ Ω hΩ (scalarToLp h1) x t := by
      simpa only [mul_one] using heq
    exact ⟨hi,heq'.trans_le hb⟩
  · have hz : dirichletKernelCandidate g hK μ hμ Ω hΩ t x = fun _ => (0 : ℝ) := by
      funext y
      exact dirichletKernelCandidate_zero_off g hK μ hμ Ω hΩ ht x y (Or.inl hx)
    rw [hz]
    simp

/-- The exact integrability and mass clause holds on every actual smooth
precompact domain for the same kernel chosen before all sources. -/
theorem dirichletKernelCandidate_mass (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : SmoothPrecompactDomain Ω)
    {t : ℝ} (ht : 0 < t) (x : M.Carrier) :
    Integrable (dirichletKernelCandidate g hK μ hμ Ω hΩ.1 t x) μ ∧
      (∫ y, dirichletKernelCandidate g hK μ hμ Ω hΩ.1 t x y ∂μ) ≤ 1 :=
  dirichletKernelCandidate_mass_of_finite g hK μ hμ Ω hΩ.1
    (smoothPrecompactDomain_volume_lt_top g μ hμ Ω hΩ) ht x

end Yau.Proofs.F03Aux
