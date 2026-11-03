import Yau.Proofs.F03DirichletHeatRepresentative
import Yau.Proofs.F03DirichletHeatPositivity
import Yau.Proofs.F03PointwiseOrder
import Yau.Proofs.F03PositiveDimension

/-! The unique actual classical interior representative of supported heat. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- A choice from the proved actual representative construction, made for
the fixed supported semigroup and no caller-supplied regularity data. -/
def dirichletClassicalHeat (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω)) : M.Carrier → ℝ → ℝ :=
  (dirichletHeat_exists_globalRepresentative (complexManifold_dimension_pos M) g hK μ hμ Ω hΩ f).choose

theorem dirichletClassicalHeat_smooth (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω)) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (fun p : Parabolic.Point n => dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv a p.1) p.2)
      ({z | z ∈ chartTarget a ∧ chartInv a z ∈ Ω} ×ˢ Set.Ioi 0) :=
  (dirichletHeat_exists_globalRepresentative (complexManifold_dimension_pos M) g hK μ hμ Ω hΩ f).choose_spec.1 a

theorem dirichletClassicalHeat_ae (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω)) {t : ℝ} (ht : 0 < t) :
    (fun y => dirichletClassicalHeat g hK μ hμ Ω hΩ f y t) =ᵐ[μ.restrict Ω]
      (dirichletHeat g μ hμ Ω t f : M.Carrier → ℝ) :=
  (dirichletHeat_exists_globalRepresentative (complexManifold_dimension_pos M) g hK μ hμ Ω hΩ f).choose_spec.2.1 t ht

theorem dirichletClassicalHeat_zero_outside (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (y : M.Carrier) (hy : y ∉ Ω) (t : ℝ) : dirichletClassicalHeat g hK μ hμ Ω hΩ f y t = 0 :=
  (dirichletHeat_exists_globalRepresentative (complexManifold_dimension_pos M) g hK μ hμ Ω hΩ f).choose_spec.2.2.1 y hy t

/-- Interior chart smoothness implies genuine continuity on Ω. -/
theorem dirichletClassicalHeat_continuousOn (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω)) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fun y => dirichletClassicalHeat g hK μ hμ Ω hΩ f y t) Ω := by
  intro x hx
  have hp : (chartPt x x,t) ∈ {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω} ×ˢ Set.Ioi 0 := by
    refine ⟨⟨mem_extChartAt_target x,?_⟩,ht⟩
    rw [show chartInv x (chartPt x x) = x from
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)]
    exact hx
  have hc := (dirichletClassicalHeat_smooth g hK μ hμ Ω hΩ f x).continuousOn.continuousAt
    (((dirichletChartInterior_open Ω hΩ x).prod isOpen_Ioi).mem_nhds hp)
  have hmap : ContinuousAt (fun y : M.Carrier => (chartPt x y,t)) x :=
    (continuousAt_extChartAt (I := ComplexModel n) x).prodMk continuousAt_const
  have hcomp : ContinuousAt (fun y : M.Carrier =>
      dirichletClassicalHeat g hK μ hμ Ω hΩ f (chartInv x (chartPt x y)) t) x :=
    hc.comp (f := fun y : M.Carrier => (chartPt x y,t)) hmap
  apply ContinuousAt.continuousWithinAt
  apply hcomp.congr
  filter_upwards [(isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds
    (mem_extChartAt_source x)] with y hy
  exact congrArg (fun z => dirichletClassicalHeat g hK μ hμ Ω hΩ f z t)
    ((extChartAt (ComplexModel n) x).left_inv hy)

/-- Positivity of the actual L² semigroup upgrades to every interior point. -/
theorem dirichletClassicalHeat_nonneg (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f : Lp ℝ 2 (μ.restrict Ω))
    (hf : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ f x) {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Ω, 0 ≤ dirichletClassicalHeat g hK μ hμ Ω hΩ f x t := by
  apply leOn_open_of_riemannian_ae_le g μ hμ Ω hΩ (fun _ => 0) _ continuousOn_const
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ f ht)
  filter_upwards [dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f ht,
    dirichletHeat_nonneg g μ hμ Ω hΩ.measurableSet ht.le f hf] with x hx hp
  rwa [hx]

/-- Choice of representatives preserves actual heat linearity, by full
support and continuity, rather than coordinated choices of local solutions. -/
theorem dirichletClassicalHeat_add (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (f k : Lp ℝ 2 (μ.restrict Ω))
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Ω, dirichletClassicalHeat g hK μ hμ Ω hΩ (f+k) x t =
      dirichletClassicalHeat g hK μ hμ Ω hΩ f x t + dirichletClassicalHeat g hK μ hμ Ω hΩ k x t := by
  apply eqOn_open_of_riemannian_ae_eq g μ hμ Ω hΩ _ _
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ (f+k) ht)
    ((dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ f ht).add
      (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ k ht))
  have hsum := dirichletClassicalHeat_ae g hK μ hμ Ω hΩ (f+k) ht
  rw [map_add] at hsum
  filter_upwards [hsum,dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f ht,
    dirichletClassicalHeat_ae g hK μ hμ Ω hΩ k ht,
    Lp.coeFn_add (dirichletHeat g μ hμ Ω t f) (dirichletHeat g μ hμ Ω t k)] with x hs hf hk ha
  simp only [hs,ha,Pi.add_apply,hf,hk]

theorem dirichletClassicalHeat_smul (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) (c : ℝ) (f : Lp ℝ 2 (μ.restrict Ω))
    {t : ℝ} (ht : 0 < t) :
    ∀ x ∈ Ω, dirichletClassicalHeat g hK μ hμ Ω hΩ (c • f) x t =
      c * dirichletClassicalHeat g hK μ hμ Ω hΩ f x t := by
  apply eqOn_open_of_riemannian_ae_eq g μ hμ Ω hΩ _ _
    (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ (c • f) ht)
    (continuousOn_const.mul (dirichletClassicalHeat_continuousOn g hK μ hμ Ω hΩ f ht))
  have hsmul := dirichletClassicalHeat_ae g hK μ hμ Ω hΩ (c • f) ht
  rw [map_smul] at hsmul
  filter_upwards [hsmul,dirichletClassicalHeat_ae g hK μ hμ Ω hΩ f ht,
    Lp.coeFn_smul c (dirichletHeat g μ hμ Ω t f)] with x hs hf hc
  simp only [hs,hc,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,hf]

end Yau.Proofs.F03Aux
