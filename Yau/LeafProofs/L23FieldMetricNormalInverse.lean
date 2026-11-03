import Yau.LeafProofs.L23FieldMetricGaussSpeed
import Yau.LeafProofs.L23FieldMetricNormalPhaseEndpoint

/-! Differentiation along the actual inverse endpoint chart. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem endpoint_inverse_fiber
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (g : ComplexVector n × ComplexVector n → ComplexVector n)
    (he : Set.EqOn e (fun p => (p.1,g p)) e.source)
    {z y : ComplexVector n} (hy : (z,y) ∈ e.target) :
    (e.symm (z,y)).1 = z ∧ (z,(e.symm (z,y)).2) ∈ e.source ∧
      g (z,(e.symm (z,y)).2) = y := by
  have H := (he (e.map_target hy)).symm.trans (e.right_inv hy)
  have Hfirst := congrArg Prod.fst H
  refine ⟨Hfirst,?_,?_⟩
  · have Hp : (z,(e.symm (z,y)).2) = e.symm (z,y) := Prod.ext Hfirst.symm rfl
    rw [Hp]
    exact e.map_target hy
  · have Hlast := congrArg Prod.snd H
    change g (e.symm (z,y)) = y at Hlast
    have Hp : (z,(e.symm (z,y)).2) = e.symm (z,y) := Prod.ext Hfirst.symm rfl
    rw [Hp]
    exact Hlast

theorem normalEndpoint_inverse_radius_hasDerivAt
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (B : Set (ComplexVector n)) (hB : IsOpen B) {ρ ε d : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (η : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (hsource : e.source = B ×ˢ Metric.ball (0 : ComplexVector n) ρ)
    (he : Set.EqOn e (fun p => (p.1,(η p 1).1)) e.source)
    (hinv : ContDiffOn ℝ 3 e.symm e.target)
    (hη : ContDiffOn ℝ 2 (Function.uncurry η)
      ((B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-ε) (1+ε)))
    (hi : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ, η p 0 = p)
    (hs : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ,
      ∀ u ∈ Set.Ioo (-ε) (1+ε), (η p u).1 ∈ chartTarget c ∧
        HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u)
    (z : ComplexVector n) {b : ℝ → ComplexVector n} {b' : ComplexVector n} {t : ℝ}
    (hb : HasDerivAt b b' t) (htarget : (z,b t) ∈ e.target) :
    let a : ℝ → ComplexVector n := fun u => (e.symm (z,b u)).2
    HasDerivAt (fun u => regularizedChartRadius h c z d (a u))
      (realMetricInChart h c z (a t) (deriv a t)/regularizedChartRadius h c z d (a t)) t ∧
    |realMetricInChart h c z (a t) (deriv a t)/regularizedChartRadius h c z d (a t)| ≤
      chartVectorNorm h c (b t) b' := by
  intro a
  have hparam : HasDerivAt (fun u => (z,b u)) (0,b') t := (hasDerivAt_const t z).prodMk hb
  have hInvD := ((hinv.contDiffAt (e.open_target.mem_nhds htarget)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t hparam
  have hA : HasDerivAt a (deriv a t) t :=
    ((ContinuousLinearMap.snd ℝ (ComplexVector n) (ComplexVector n)).hasFDerivAt.comp_hasDerivAt
      t hInvD).differentiableAt.hasDerivAt
  refine ⟨regularizedChartRadius_hasDerivAt h c z hd hA,?_⟩
  have Hfiber := endpoint_inverse_fiber e (fun p => (η p 1).1) he htarget
  have hp : (z,a t) ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ := by
    rw [← hsource]
    exact Hfiber.2.1
  have h₁ : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hP : ((z,a t),(1 : ℝ)) ∈
      (B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-ε) (1+ε) := ⟨hp,h₁⟩
  have Hη : ContDiffAt ℝ 2 (Function.uncurry η) ((z,a t),(1 : ℝ)) :=
    hη.contDiffAt (((hB.prod Metric.isOpen_ball).prod isOpen_Ioo).mem_nhds hP)
  have hEmbed : ContDiffAt ℝ 2 (fun v : ComplexVector n => ((z,v),(1 : ℝ))) (a t) := by fun_prop
  have hEndPhase : ContDiffAt ℝ 2 (fun v : ComplexVector n => η (z,v) 1) (a t) :=
    ContDiffAt.comp (g := Function.uncurry η)
      (f := fun v : ComplexVector n => ((z,v),(1 : ℝ))) (a t) Hη hEmbed
  have hEndC : ContDiffAt ℝ 2 (fun v : ComplexVector n => (η (z,v) 1).1) (a t) := hEndPhase.fst
  have hEndD : DifferentiableAt ℝ (fun v => (η (z,v) 1).1) (a t) :=
    hEndC.differentiableAt (by norm_num)
  have hED := hEndD.hasFDerivAt.comp_hasDerivAt t hA
  have hEq : b =ᶠ[𝓝 t] (fun u => (η (z,a u) 1).1) := by
    filter_upwards [hparam.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds htarget)] with u hu
    exact (endpoint_inverse_fiber e (fun p => (η p 1).1) he hu).2.2.symm
  have hspeed : fderiv ℝ (fun v => (η (z,v) 1).1) (a t) (deriv a t) = b' :=
    (hED.congr_of_eventuallyEq hEq).unique hb
  have H := chartGeodesicFamily_regularized_radius_bound h hh c B hB hε hd η hη hi hs
    hp.1 hp.2 (deriv a t)
  rw [Hfiber.2.2,hspeed] at H
  exact H

end Yau.LeafProofs.L23Aux
