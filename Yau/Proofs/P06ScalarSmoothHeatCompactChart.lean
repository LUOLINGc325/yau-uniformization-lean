import Yau.Proofs.P06ScalarSmoothHeatCompactWords
import Yau.Proofs.P06ScalarSmoothHeatLinearLimits

/-! The complete compact chart derivative norm tends to zero for
compact smooth data, in every form degree and every fiber coordinate. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeHeat_compact_initial_finite_coord {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (U : ℝ → RealForm M k) (hU : ∀ t, 0 < t → SmoothRealForm (U t))
    (hUL : ∀ t, 0 < t → L2RealForm g.form μ (U t))
    (hUr : ∀ t ht, realizeActualForm g μ (U t) (hUL t ht) =
      hodgeHeatHilbert g μ hμ k t (compactHodgeIterateHilbert g μ hμ A hA hcA 0))
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ y,
      ‖iteratedFDeriv ℝ j (fun z => χ ((hodgeRegularityFinEquiv n).symm z) *
        hodgeRegularityCoord b (U t-A) x ((hodgeRegularityFinEquiv n).symm z) c) y‖ < ε := by
  apply iteratedFDeriv_uniform_small_of_words (Pi.basisFun ℝ _) _ _ _ j ε hε
  · intro t ht
    have hsD : SmoothRealForm (U t-A) := fun a I => (hU t ht a I).sub (hA a I)
    exact (scalar_cutoff_contDiff_properties
      (isOpen_extChartAt_target (I := ComplexModel n) x) χ hχ hcχ hχO _
      (hodgeRegularityCoord_contDiffOn b (U t-A) hsD x c)).1.comp
        (hodgeRegularityFinEquiv n).symm.contDiff
  · intro w δ hδ
    have hb : (Pi.basisFun ℝ (Fin (Fintype.card (RIdx n))) :
        Fin (Fintype.card (RIdx n)) → (Fin (Fintype.card (RIdx n)) → ℝ)) =
        fun i => Pi.single i 1 := funext (Pi.basisFun_apply ℝ _)
    rw [hb]
    exact hodgeHeat_compact_initial_chart_word
      g μ hμ A hA hcA U hU hUL hUr x b χ hχ hcχ hχO c w δ hδ

theorem hodgeHeat_compact_initial_chart_coord {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (U : ℝ → RealForm M k) (hU : ∀ t, 0 < t → SmoothRealForm (U t))
    (hUL : ∀ t, 0 < t → L2RealForm g.form μ (U t))
    (hUr : ∀ t ht, realizeActualForm g μ (U t) (hUL t ht) =
      hodgeHeatHilbert g μ hμ k t (compactHodgeIterateHilbert g μ hμ A hA hcA 0))
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w => χ w * hodgeRegularityCoord b (U t-A) x w c) z‖ < ε := by
  let e := (hodgeRegularityFinEquiv n).toContinuousLinearMap
  let C := (‖e‖+1)^j
  have hC : 0 < C := pow_pos (by positivity) _
  obtain ⟨τ,hτ,hh⟩ := hodgeHeat_compact_initial_finite_coord g μ hμ A hA hcA
    U hU hUL hUr x b χ hχ hcχ hχO c j (ε/C) (div_pos hε hC)
  refine ⟨τ,hτ,?_⟩
  intro t ht htτ z
  let F := fun y => χ ((hodgeRegularityFinEquiv n).symm y) *
    hodgeRegularityCoord b (U t-A) x ((hodgeRegularityFinEquiv n).symm y) c
  have hsD : SmoothRealForm (U t-A) := fun a I => (hU t ht a I).sub (hA a I)
  have hsF : ContDiff ℝ ∞ F := (scalar_cutoff_contDiff_properties
    (isOpen_extChartAt_target (I := ComplexModel n) x) χ hχ hcχ hχO _
    (hodgeRegularityCoord_contDiffOn b (U t-A) hsD x c)).1.comp
      (hodgeRegularityFinEquiv n).symm.contDiff
  have he := iteratedFDeriv_comp_linear_bound e F hsF j z
  have hfun : F ∘ e = fun w => χ w * hodgeRegularityCoord b (U t-A) x w c := by
    funext w
    simp only [Function.comp_def,F,e,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [hfun] at he
  have hp : ‖e‖^j ≤ C := by
    dsimp only [C]
    gcongr
    linarith
  calc
    _ ≤ ‖iteratedFDeriv ℝ j F (e z)‖ * ‖e‖^j := he
    _ ≤ ‖iteratedFDeriv ℝ j F (e z)‖ * C :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ < (ε/C) * C := mul_lt_mul_of_pos_right (hh t ht htτ (e z)) hC
    _ = ε := div_mul_cancel₀ _ hC.ne'

end Yau.NodeProofs.P06Aux.ScalarSmooth
