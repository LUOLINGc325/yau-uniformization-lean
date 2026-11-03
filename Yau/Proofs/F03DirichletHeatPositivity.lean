import Yau.Proofs.F03DirichletHeatMarkov
import Yau.LeafProofs.L19HeatMarkovPositivity

/-! Actual supported heat positivity for every L² input and zero-endpoint bounds. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {M : ComplexManifold n}

/-- Native bounded clips approximate every nonnegative actual L² input;
continuity and the closed L² positive cone give positivity of the same heat. -/
theorem dirichletHeat_nonneg (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 ≤ t) (f : Lp ℝ 2 (μ.restrict Ω))
    (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x) :
    ∀ᵐ x ∂μ.restrict Ω, 0 ≤ dirichletHeat g μ hμ Ω t f x := by
  have hlim := (dirichletHeat g μ hμ Ω t).continuous.continuousAt.tendsto.comp
    (normalClipL2_tendsto_of_nonneg (μ.restrict Ω) f hf)
  have hbound (k : ℕ) : 0 ≤ dirichletHeat g μ hμ Ω t
      (normalClipL2 (μ.restrict Ω) ((k : ℝ) + 1) (by positivity) f) := by
    apply (Lp.coeFn_nonneg _).mp
    have hfclip : ∀ᵐ x ∂μ.restrict Ω,
        0 ≤ normalClipL2 (μ.restrict Ω) ((k : ℝ) + 1) (by positivity) f x ∧
        normalClipL2 (μ.restrict Ω) ((k : ℝ) + 1) (by positivity) f x ≤ (k : ℝ) + 1 := by
      filter_upwards [normalClipL2_coe (μ.restrict Ω) ((k : ℝ) + 1) (by positivity) f] with x hx
      rw [hx]
      exact normalClip_mem_interval (by positivity) _
    exact (dirichletHeat_markov g μ hμ Ω hΩ ht ((k : ℝ) + 1) (by positivity) _ hfclip).mono
      (fun _ h => h.1)
  apply (Lp.coeFn_nonneg _).mpr
  exact (isClosed_Ici : IsClosed {v : Lp ℝ 2 (μ.restrict Ω) | 0 ≤ v}).mem_of_tendsto hlim
    (Eventually.of_forall hbound)

/-- Positivity and actual linearity make the supported heat order preserving. -/
theorem dirichletHeat_monotone (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 ≤ t) : Monotone (dirichletHeat g μ hμ Ω t) := by
  intro f k hfk
  have hdiff : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ (k-f) x :=
    (Lp.coeFn_nonneg _).mpr (sub_nonneg.mpr hfk)
  have h := (Lp.coeFn_nonneg _).mp (dirichletHeat_nonneg g μ hμ Ω hΩ ht (k-f) hdiff)
  rw [map_sub] at h
  exact sub_nonneg.mp h

/-- The genuine Markov interval includes its zero numerical endpoint. -/
theorem dirichletHeat_submarkov (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) (hΩ : MeasurableSet Ω)
    {t : ℝ} (ht : 0 ≤ t) (K : ℝ) (hK : 0 ≤ K) (f : Lp ℝ 2 (μ.restrict Ω))
    (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x ∧ f x ≤ K) :
    ∀ᵐ x ∂μ.restrict Ω, 0 ≤ dirichletHeat g μ hμ Ω t f x ∧
      dirichletHeat g μ hμ Ω t f x ≤ K := by
  rcases hK.eq_or_lt with rfl | hK
  · have hf0 : f = 0 := by
      apply Lp.ext
      filter_upwards [hf,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict Ω)] with x hx hzero
      exact (le_antisymm hx.2 hx.1).trans hzero.symm
    have hTf : dirichletHeat g μ hμ Ω t f = (0 : Lp ℝ 2 (μ.restrict Ω)) := by rw [hf0,map_zero]
    rw [hTf]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict Ω)] with x hx
    rw [hx]
    exact ⟨le_rfl,le_rfl⟩
  · exact dirichletHeat_markov g μ hμ Ω hΩ ht K hK f hf

end Yau.Proofs.F03Aux
