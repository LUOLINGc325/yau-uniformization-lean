import Yau.Proofs.F03AmbientCoerciveForm
import Yau.Proofs.F03ResolventPositivity
import Yau.Proofs.F03ExhaustionStepL2
import Yau.Proofs.F04AmbientShiftPairings
import Yau.Proofs.F04SupportedInclusion

/-! Domain-to-ambient domination of the actual positive-step resolvents. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau F04Proof LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

theorem dirichlet_step_le_ambient_weak_solution (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {h : ℝ} (hh : 0 < h)
    (f : Lp ℝ 2 μ) (q : ScalarEnergySpace g μ hμ)
    (hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x)
    (hqeq : ∀ v : DirichletEnergy g μ hμ Ω, scalarResolventForm g μ hμ h q v.val=
      inner ℝ f (scalarEnergyL2 g μ hμ v.val)) :
    ∀ᵐ x ∂μ, scalarEnergyL2 g μ hμ
      (dirichletStepResolventEnergy g μ hμ Ω h hh (l2Restriction μ Ω f)).val x ≤
      scalarEnergyL2 g μ hμ q x := by
  let u := dirichletStepResolventEnergy g μ hμ Ω h hh (l2Restriction μ Ω f)
  let w := dirichletAmbientShiftPosPart g hK μ hμ Ω hΩ u q hq
  have hpair := dirichletAmbientShiftPosPart_global_pairings g hK μ hμ Ω hΩ u q hq
  have hu : scalarResolventForm g μ hμ h u.val w.val=
      inner ℝ f (scalarEnergyL2 g μ hμ w.val) :=
    dirichlet_step_ambient_equation g μ hμ Ω hΩ.measurableSet hh f w
  have hqe := hqeq w
  have hzero : scalarResolventForm g μ hμ h (u.val-q) w.val=0 := by
    rw [map_sub,sub_apply,hu,hqe,sub_self]
  rw [scalarResolventForm_apply,scalarClosedEnergy_eq_univ_differential] at hzero
  simp only [map_sub] at hzero
  rw [hpair.1,hpair.2] at hzero
  have hJzero : scalarEnergyL2 g μ hμ w.val=0 := by
    apply norm_eq_zero.mp
    have hnonneg : 0 ≤ h*((1/2 : ℝ)*‖scalarEnergyD g μ hμ Set.univ w.val‖^2) :=
      mul_nonneg hh.le (mul_nonneg (by norm_num) (sq_nonneg _))
    nlinarith only [hzero,hnonneg,norm_nonneg (scalarEnergyL2 g μ hμ w.val)]
  have hpartzero : Lp.posPart (scalarEnergyL2 g μ hμ u.val-scalarEnergyL2 g μ hμ q)=0 :=
    (dirichletAmbientShiftPosPart_ambient_L2 g hK μ hμ Ω hΩ u q hq).symm.trans hJzero
  have hpartae := Lp.ext_iff.mp hpartzero
  have horder : ∀ᵐ x ∂μ, scalarEnergyL2 g μ hμ u.val x ≤ scalarEnergyL2 g μ hμ q x := by
    filter_upwards [hpartae,
      Lp.coeFn_posPart (scalarEnergyL2 g μ hμ u.val-scalarEnergyL2 g μ hμ q),
      Lp.coeFn_sub (scalarEnergyL2 g μ hμ u.val) (scalarEnergyL2 g μ hμ q),
      Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hzero hp hs hz
    have hmax : max (scalarEnergyL2 g μ hμ u.val x-scalarEnergyL2 g μ hμ q x) 0=0 := by
      rw [hp,hs,Pi.sub_apply,hz] at hzero
      exact hzero
    have hdiff := le_max_left (scalarEnergyL2 g μ hμ u.val x-scalarEnergyL2 g μ hμ q x) 0
    rw [hmax] at hdiff
    exact sub_nonpos.mp hdiff
  exact horder

theorem dirichletAmbientStep_le_scalarResolvent (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (Ω : Set M.Carrier) (hΩ : IsOpen Ω) {h : ℝ} (hh : 0 < h)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ∀ᵐ x ∂μ, dirichletAmbientStep g μ hμ Ω hΩ.measurableSet h hh f x ≤
      scalarResolvent g μ hμ h hh f x := by
  let q := scalarResolventEnergy g μ hμ h hh f
  have hq : ∀ᵐ x ∂μ, 0 ≤ scalarEnergyL2 g μ hμ q x := scalarResolvent_nonneg g μ hμ hh f hf
  have hqeq (v : DirichletEnergy g μ hμ Ω) : scalarResolventForm g μ hμ h q v.val=
      inner ℝ f (scalarEnergyL2 g μ hμ v.val) := by
    simpa only [q,scalarResolventForm_apply,scalarResolvent,ContinuousLinearMap.comp_apply] using
      scalarResolventEnergy_equation g μ hμ h hh f v.val
  rw [dirichletAmbientStep_eq_energy]
  exact dirichlet_step_le_ambient_weak_solution g hK μ hμ Ω hΩ hh f q hq hqeq

end Yau.Proofs.F03Aux
