import Yau.LeafProofs.L17BootstrapCompactCoefficientsBounds
import Yau.LeafProofs.L17BootstrapHolderTaylorFinite
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual mixed parameter jets are continuous and bounded on one fixed compact box. -/

noncomputable section
open Set Metric
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Yau.LeafProofs.L17BootstrapCompactCoefficientsAux
open L17Aux L17BootstrapHolderTaylorAux

variable {Param E F : Type*}
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def singleParamJet (c : Param → E → ℝ → F) (k : ℕ) (theta : Param) (z : E) (t : ℝ) :
    ParamJet Param k F := iteratedFDeriv ℝ k (fun a => c a z t) theta

def spaceInjection (Param E : Type*) [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    [NormedAddCommGroup E] [NormedSpace ℝ E] : E →L[ℝ] Param × (E × ℝ) :=
  (0 : E →L[ℝ] Param).prod ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ))

theorem singleParamJet_contDiffAt {c : Param → E → ℝ → F} {p : Param × (E × ℝ)}
    (hc : ContDiffAt ℝ ∞ (fun a : Param × (E × ℝ) => c a.1 a.2.1 a.2.2) p) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun a : Param × (E × ℝ) => singleParamJet c k a.1 a.2.1 a.2.2) p :=
  contDiffAt_parameterJet (c := fun a (b : E × ℝ) => c a b.1 b.2) (p := p) hc k

theorem singleParamJet_space_fderiv {c : Param → E → ℝ → F} {theta : Param} {z : E} {t : ℝ}
    (hc : ContDiffAt ℝ ∞ (fun a : Param × (E × ℝ) => c a.1 a.2.1 a.2.2) (theta,(z,t)))
    (k : ℕ) :
    fderiv ℝ (fun w => singleParamJet c k theta w t) z =
      (fderiv ℝ (fun a : Param × (E × ℝ) => singleParamJet c k a.1 a.2.1 a.2.2)
        (theta,(z,t))).comp (spaceInjection Param E) := by
  have hcurve : HasFDerivAt (fun w : E => (theta,(w,t))) (spaceInjection Param E) z :=
    (hasFDerivAt_const theta z).prodMk ((hasFDerivAt_id z).prodMk (hasFDerivAt_const t z))
  exact (((singleParamJet_contDiffAt hc k).differentiableAt (by simp)).hasFDerivAt.comp z hcurve).fderiv

theorem singleParamJet_time_deriv {c : Param → E → ℝ → F} {theta : Param} {z : E} {t : ℝ}
    (hc : ContDiffAt ℝ ∞ (fun a : Param × (E × ℝ) => c a.1 a.2.1 a.2.2) (theta,(z,t)))
    (k : ℕ) :
    deriv (fun s => singleParamJet c k theta z s) t =
      fderiv ℝ (fun a : Param × (E × ℝ) => singleParamJet c k a.1 a.2.1 a.2.2)
        (theta,(z,t)) (0,(0,1)) := by
  have hcurve : HasDerivAt (fun s : ℝ => (theta,(z,s))) (0,(0,1)) t :=
    (hasDerivAt_const t theta).prodMk ((hasDerivAt_const t z).prodMk (hasDerivAt_id t))
  exact (((singleParamJet_contDiffAt hc k).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hcurve).deriv

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

/-- Compactness chooses every ordinary mixed budget on the same closed parameter
ball and the same closed time interval. No radius depends on k. -/
theorem exists_compact_mixed_budgets [ProperSpace Param]
    (P : UniformChartPartition g) {R Rout T : ℝ} (hRRout : R < Rout)
    (c : Param → ComplexVector n → ℝ → F)
    (hSmooth : ContDiffOn ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => c a.1 a.2.1 a.2.2)
      (ball 0 Rout ×ˢ (ball 0 (2*P.radius) ×ˢ Set.univ))) :
    ∃ B : ℕ → ℝ, ∀ k, 0 ≤ B k ∧
      ∀ theta ∈ closedBall 0 R, ∀ z ∈ closedBall 0 P.radius, ∀ t ∈ Icc (0:ℝ) T,
        ‖singleParamJet c k theta z t‖ ≤ B k ∧
        ‖fderiv ℝ (fun w => singleParamJet c k theta w t) z‖ ≤ B k ∧
        ‖deriv (fun s => singleParamJet c k theta z s) t‖ ≤ B k := by
  let K := compactMixedBox Param (ComplexVector n) R P.radius T
  have hK : IsCompact K := isCompact_compactMixedBox Param (ComplexVector n) R P.radius T
  have hOpen : IsOpen (ball (0:Param) Rout ×ˢ
      (ball (0:ComplexVector n) (2*P.radius) ×ˢ (univ : Set ℝ))) :=
    isOpen_ball.prod (isOpen_ball.prod isOpen_univ)
  have hKsub : K ⊆ ball (0:Param) Rout ×ˢ
      (ball (0:ComplexVector n) (2*P.radius) ×ˢ (univ : Set ℝ)) := by
    intro p hp
    change p.1 ∈ closedBall (0:Param) R ∧ p.2.1 ∈ closedBall (0:ComplexVector n) P.radius ∧
      p.2.2 ∈ Icc (0:ℝ) T at hp
    have ha : ‖p.1‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hp.1
    have hz : ‖p.2.1‖ ≤ P.radius := by simpa only [mem_closedBall,dist_zero_right] using hp.2.1
    refine ⟨?_,?_,mem_univ _⟩
    · simpa only [mem_ball,dist_zero_right] using ha.trans_lt hRRout
    · simpa only [mem_ball,dist_zero_right] using hz.trans_lt (by linarith [P.radius_pos] : P.radius < 2*P.radius)
  have hc : ∀ p ∈ K, ContDiffAt ℝ ∞
      (fun a : Param × (ComplexVector n × ℝ) => c a.1 a.2.1 a.2.2) p :=
    fun p hp => hSmooth.contDiffAt (hOpen.mem_nhds (hKsub hp))
  let J := fun k (p : Param × (ComplexVector n × ℝ)) => singleParamJet c k p.1 p.2.1 p.2.2
  have hj : ∀ k p, p ∈ K → ContDiffAt ℝ ∞ (J k) p :=
    fun k p hp => singleParamJet_contDiffAt (hc p hp) k
  have h0 : ∀ k, ContinuousOn (J k) K :=
    fun k p hp => (hj k p hp).continuousAt.continuousWithinAt
  have hz : ∀ k, ContinuousOn
      (fun p : Param × (ComplexVector n × ℝ) =>
        fderiv ℝ (fun w => singleParamJet c k p.1 w p.2.2) p.2.1) K := by
    intro k
    have hd : ContinuousOn (fun p => (fderiv ℝ (J k) p).comp (spaceInjection Param (ComplexVector n))) K := by
      intro p hp
      exact (((hj k p hp).fderiv_right (by simp : (∞ : ℕ∞ω)+1 ≤ ∞)).clm_comp
        contDiffAt_const).continuousAt.continuousWithinAt
    apply hd.congr
    intro p hp
    exact singleParamJet_space_fderiv (hc p hp) k
  have ht : ∀ k, ContinuousOn
      (fun p : Param × (ComplexVector n × ℝ) => deriv (fun s => singleParamJet c k p.1 p.2.1 s) p.2.2) K := by
    intro k
    have hd : ContinuousOn (fun p => fderiv ℝ (J k) p (0,(0,1))) K := by
      intro p hp
      exact (((hj k p hp).fderiv_right (by simp : (∞ : ℕ∞ω)+1 ≤ ∞)).clm_apply
        contDiffAt_const).continuousAt.continuousWithinAt
    apply hd.congr
    intro p hp
    exact singleParamJet_time_deriv (hc p hp) k
  obtain ⟨B,hB⟩ := exists_order_budgets hK J
    (fun k (p : Param × (ComplexVector n × ℝ)) => fderiv ℝ (fun w => singleParamJet c k p.1 w p.2.2) p.2.1)
    (fun k (p : Param × (ComplexVector n × ℝ)) => deriv (fun s => singleParamJet c k p.1 p.2.1 s) p.2.2)
    h0 hz ht
  refine ⟨B,?_⟩
  intro k
  exact ⟨(hB k).1,fun theta htheta z hz t ht => (hB k).2 (theta,(z,t)) ⟨htheta,hz,ht⟩⟩

end Yau.LeafProofs.L17BootstrapCompactCoefficientsAux
