import Yau.Proofs.V02CostMixed
import Yau.Proofs.V02DataTransport
import Yau.Proofs.V02TestQuadraticLossBounds
import Yau.Proofs.V02BoundaryQuadraticContinuous

/-! The actual whole mixed derivative gives the original quadratic test
up to auxiliary damping loss. Its penalty coefficient precedes the test. -/

open scoped Topology ContDiff Matrix
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof V02CostMixedProof

variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_mixed_test_loss_coefficient {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : CotangentPoint X.manifold → ℝ → ℝ,
      StrictEnvelopeContact {d with test := φ} → ∃ M : ℝ, 0 ≤ M ∧
      ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
        (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
        (fz : ℂ → ℂ → CotangentPoint X.manifold) (r ε η : ℝ),
        AdmissibleVariationDisc {d with test := φ} j F →
        NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
        (∀ ζ ∈ closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
        RealizesFirstField {d with test := φ} j a F E l h α fz r →
        (α 0).im = 0 → 0 < (α 0).re → -Real.log (α 0).re ≤ η →
        circleAverage (fun θ => 1 - ‖α (circlePoint θ)‖ ^ 2) ≤ η → 0 ≤ ε →
        outerCenter d j a F ^ 2 * quadValue
          (centerTestHessian {d with test := φ} F E) (l 0) -
          circleAverage (fun θ => quadValue (boundarySymbol d j a F E (circlePoint θ))
            (l (circlePoint θ))) -
          C * ε * (1 + (variationEnergy d j F).toReal +
            (boundaryDSq (fun θ => l (circlePoint θ))).toReal) ≤
          -mixedReal (fun z => penalizedFunctional {d with test := φ} j ε
            {F with f := fz z}) + M * η := by
  obtain ⟨C, hC, henergy⟩ := energyCoefficient_before_test hd j a ha L hL
  refine ⟨C, hC, fun φ hφ => ?_⟩
  have hdφ := variationSetup_update_test hd φ hφ
  obtain ⟨M₀, M₁, hM₀, hM₁, hquadratic⟩ := test_quadratic_loss_bounds hdφ j a ha L
  refine ⟨2 * M₀ + M₁, by positivity, fun F E l h α fz r ε η hF hE hl hsup hR
    hphase hpos hlog hloss hε => ?_⟩
  have hquad := hquadratic F E l hF hE hsup
  have hα : ContDiffOn ℂ ∞ α (closedBall (0 : ℂ) 1) := hR.2.2.2.2.1
  have hαsup : ∀ ζ ∈ closedBall (0 : ℂ) 1, ‖α ζ‖ ≤ 1 := hR.2.2.2.2.2.2.2.2.1
  have hn : ‖α 0‖ = (α 0).re := by
    have heq : α 0 = ((α 0).re : ℂ) := Complex.ext (by simp) (by simpa using hphase)
    calc
      ‖α 0‖ = ‖((α 0).re : ℂ)‖ := congrArg norm heq
      _ = (α 0).re := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  have ht1 : (α 0).re ≤ 1 := by rw [← hn]; exact hαsup 0 (by simp)
  have hw : Continuous (fun θ => ‖α (circlePoint θ)‖ ^ 2) :=
    (hα.continuousOn.comp_continuous circlePoint_contDiff.continuous circlePoint_mem_closedBall).norm.pow 2
  have hw1 (θ : ℝ) : ‖α (circlePoint θ)‖ ^ 2 ≤ 1 := by
    have hh := hαsup _ (circlePoint_mem_closedBall θ)
    nlinarith [norm_nonneg (α (circlePoint θ))]
  have hb := damped_boundary_average_loss hw
    (boundary_quadratic_continuous hdφ j a ha F hF E hE l hl) hM₁ hw1 hquad.2 hloss
  have he := henergy φ F E l h α fz r hF hE hl hsup hR
  have he' := (le_abs_self _).trans he
  have hm := damped_quadratic_error hpos ht1 hlog hquad.1 hM₀ hb he' hε
  have hid := costMixed_identity hdφ j a F hF E l h α fz r ε hR
  rw [hn] at hid
  have hid' : mixedReal (fun z => penalizedFunctional {d with test := φ} j ε
      {F with f := fz z}) =
      circleAverage (fun θ => ‖α (circlePoint θ)‖ ^ 2 *
        quadValue (boundarySymbol d j a F E (circlePoint θ)) (l (circlePoint θ))) -
      (α 0).re ^ 2 * (outerCenter d j a F ^ 2 *
        quadValue (centerTestHessian {d with test := φ} F E) (l 0)) +
      ε * mixedReal (fun z => (variationEnergy d j {F with f := fz z}).toReal) := by
    simpa only [boundarySymbol_update_test, outerCenter_update_test,
      variationEnergy_update_test, mul_assoc] using hid
  rw [hid']
  simp only [boundarySymbol_update_test, outerCenter_update_test,
    variationEnergy_update_test] at hm
  convert hm using 1 <;> ring

end Yau.Blueprint.V02Proof
