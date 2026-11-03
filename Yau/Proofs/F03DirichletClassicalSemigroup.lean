import Yau.Proofs.F03DirichletClassicalHeat
import Yau.Proofs.F03DirichletHeatInjective

/-! Actual pointwise semigroup identities and nontriviality in the interior. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual classical representative of the zero vector is zero at
every interior point, by actual slice identity and full support. -/
theorem dirichletClassicalHeat_zero (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Ω, dirichletClassicalHeat g hK μ hμ Ω hΩ 0 x t = 0 := by
  apply eqOn_open_of_riemannian_ae_eq g μ hμ Ω hΩ _ _
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ 0 ht) continuousOn_const
  have ha := dirichletClassicalHeat_ae g hK μ hμ Ω hΩ 0 ht
  rw [map_zero] at ha
  filter_upwards [ha,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict Ω)] with x hx hzero
  exact hx.trans hzero

/-- The same actual heat semigroup law holds pointwise after interior
gluing; uniqueness supplies compatibility of the chosen representatives. -/
theorem dirichletClassicalHeat_semigroup (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) :
    ∀ x ∈ Ω, dirichletClassicalHeat g hK μ hμ Ω hΩ f x (t+s) =
      dirichletClassicalHeat g hK μ hμ Ω hΩ (dirichletHeat g μ hμ Ω s f) x t := by
  have hts : 0 < t+s := add_pos_of_pos_of_nonneg ht hs
  apply eqOn_open_of_riemannian_ae_eq g μ hμ Ω hΩ _ _
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ f hts)
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ _ ht)
  have ha := dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f hts
  have hst : dirichletHeat g μ hμ Ω (t+s) f =
      dirichletHeat g μ hμ Ω t (dirichletHeat g μ hμ Ω s f) := by
    rw [dirichletHeat_add g μ hμ Ω ht.le hs,mul_apply_eq_comp]
  rw [hst] at ha
  filter_upwards [ha,dirichletClassicalHeat_ae g hK μ hμ Ω hΩ
    (dirichletHeat g μ hμ Ω s f) ht] with x hx hy
  exact hx.trans hy.symm

/-- A nonzero nonnegative actual L² input gives a strictly positive value
somewhere at every positive time. Point-to-point propagation will use the
already proved moving cubic bump and compact comparison. -/
theorem dirichletClassicalHeat_pos_somewhere (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x) (hfn : f ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∃ x ∈ Ω, 0 < dirichletClassicalHeat g hK μ hμ Ω hΩ f x t := by
  by_contra hpos
  have hz (x : M.Carrier) (hx : x ∈ Ω) :
      dirichletClassicalHeat g hK μ hμ Ω hΩ f x t = 0 := by
    have hle : dirichletClassicalHeat g hK μ hμ Ω hΩ f x t ≤ 0 :=
      le_of_not_gt (fun hp => hpos ⟨x,hx,hp⟩)
    exact le_antisymm hle (dirichletClassicalHeat_nonneg g hK μ hμ Ω hΩ f hf ht x hx)
  have hSf : dirichletHeat g μ hμ Ω t f = 0 := by
    apply Lp.ext
    filter_upwards [dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f ht,
      ae_restrict_mem hΩ.measurableSet,Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ.restrict Ω)] with x hx hxΩ hzero
    exact hx.symm.trans ((hz x hxΩ).trans hzero.symm)
  exact hfn ((dirichletHeat_zero_iff g μ hμ Ω hΩ ht f).mp hSf)

end Yau.Proofs.F03Aux
