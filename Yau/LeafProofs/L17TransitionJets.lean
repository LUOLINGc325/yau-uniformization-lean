import Yau.LeafProofs.L17TransitionJetOperator

/-! Uniform jets of every actual bounded-background transition, by the connection equation. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance transitionJets_firstGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transitionJets_firstSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transitionJets_secondGroup :
    NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance transitionJets_secondSpace :
    NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem BoundedChartFamily.transition_uniformJetBounds (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k A.transitionMap A.transitionBallDomain := by
  have hs := A.transitionBallDomain_isOpen
  have hT := A.transitionMap_contDiffOn
  have hJ (a : M.Carrier × M.Carrier) :
      ContDiffOn ℝ ∞ (fderiv ℝ (A.transitionMap a)) (A.transitionBallDomain a) :=
    (hT a).fderiv_of_isOpen (hs a) (by simp : ∞ + 1 ≤ ∞)
  have hmap (a : M.Carrier × M.Carrier) :
      MapsTo (A.transitionMap a) (A.transitionBallDomain a) (ball 0 A.radius) :=
    fun _ hz => hz.2.2
  have hP (a : M.Carrier × M.Carrier) :
      ContDiffOn ℝ ∞ (backgroundConnection g (A.chart a.1)) (A.transitionBallDomain a) :=
    (A.backgroundConnection_smooth a.1).mono (fun _ hz => hz.1)
  have hQ (a : M.Carrier × M.Carrier) :
      ContDiffOn ℝ ∞ (backgroundConnection g (A.chart a.2)) (ball 0 A.radius) :=
    A.backgroundConnection_smooth a.2
  have hQT (a : M.Carrier × M.Carrier) : ContDiffOn ℝ ∞
      (fun z => backgroundConnection g (A.chart a.2) (A.transitionMap a z))
      (A.transitionBallDomain a) := (hQ a).comp (hT a) (hmap a)
  have horders : ∀ j, ∃ C : ℝ, ∀ a z, z ∈ A.transitionBallDomain a →
      ‖iteratedFDeriv ℝ j (A.transitionMap a) z‖ ≤ C := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases hj0 : j = 0
      · subst j
        refine ⟨A.radius, ?_⟩
        intro a z hz
        rw [norm_iteratedFDeriv_zero]
        have ht : ‖A.transitionMap a z‖ < A.radius := by
          have htball : A.transitionMap a z ∈ ball 0 A.radius := hz.2.2
          simpa only [mem_ball, dist_zero_right] using htball
        exact ht.le
      by_cases hj1 : j = 1
      · subst j
        refine ⟨A.bound 0, ?_⟩
        intro a z hz
        rw [norm_iteratedFDeriv_one]
        exact A.transition_fderiv_opNorm_le a.1 a.2 hz.1 (A.transitionBallDomain_image a hz)
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
      have hbT : UniformJetBounds (m + 1) A.transitionMap A.transitionBallDomain :=
        UniformJetBounds.of_orderBounds fun l hl => ih l (by omega)
      have hbJ := hbT.fderiv
      have hbP : UniformJetBounds m
          (fun a z => backgroundConnection g (A.chart a.1) z) A.transitionBallDomain :=
        ((A.backgroundConnection_uniformJetBounds m).reindex
          (fun a : M.Carrier × M.Carrier => a.1)).mono_sets (fun _ _ hz => hz.1)
      have hbQ := (A.backgroundConnection_uniformJetBounds m).reindex
        (fun a : M.Carrier × M.Carrier => a.2)
      have hbQT := (hbT.mono_order (Nat.le_succ m)).comp hbQ hs
        (fun _ => isOpen_ball) hT hQ hmap
      have hbPQ := hbP.prodMk hbQT hs hP hQT
      have hbInput := hbJ.prodMk hbPQ hs hJ (fun a => (hP a).prodMk (hQT a))
      have hInput (a : M.Carrier × M.Carrier) := (hJ a).prodMk ((hP a).prodMk (hQT a))
      have hbSecond := hbInput.comp_global hs hInput (transitionAcceleration_contDiff (n := n))
      have hbActual : UniformJetBounds m
          (fun a => fderiv ℝ (fderiv ℝ (A.transitionMap a))) A.transitionBallDomain := by
        apply hbSecond.congr hs
        intro a z hz
        exact (A.transition_acceleration_eq a hz).symm
      obtain ⟨C, _, hC⟩ := hbActual
      refine ⟨C, ?_⟩
      intro a z hz
      simpa only [norm_iteratedFDeriv_fderiv, Nat.add_assoc] using hC a z hz m le_rfl
  exact UniformJetBounds.of_orderBounds fun j _ => horders j

theorem BoundedChartFamily.exists_transition_jet_budget (A : BoundedChartFamily g) :
    ∃ B : ℕ → ℝ, (∀ k, 0 < B k) ∧ ∀ p q k z,
      z ∈ ball 0 A.radius → A.chart p z ∈ A.chart q '' ball 0 A.radius →
      ‖iteratedFDeriv ℝ k (fun w => (A.chart q).symm (A.chart p w)) z‖ ≤ B k := by
  classical
  choose B hB hb using fun k => A.transition_uniformJetBounds k
  refine ⟨B, fun k => zero_lt_one.trans_le (hB k), ?_⟩
  intro p q k z hz hq
  have hzs : z ∈ (A.chart p).source := A.closedBall_source p (ball_subset_closedBall hz)
  obtain ⟨w, hw, hweq⟩ := hq
  have hws := A.closedBall_source q (ball_subset_closedBall hw)
  have hzt : A.chart p z ∈ (A.chart q).target := by
    rw [← hweq]
    exact (A.chart q).map_source hws
  have hwz : A.transitionMap (p, q) z = w := by
    change (A.chart q).symm (A.chart p z) = w
    rw [← hweq, (A.chart q).left_inv hws]
  have htball : A.transitionMap (p, q) z ∈ ball 0 A.radius := by rw [hwz]; exact hw
  have hdom : z ∈ A.transitionBallDomain (p, q) := ⟨hz, ⟨hzs, hzt⟩, htball⟩
  exact hb k (p, q) z hdom k le_rfl

end Yau.LeafProofs.L17Aux
