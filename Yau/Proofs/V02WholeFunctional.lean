import Yau.Proofs.V02FunctionalCalculus
import Yau.Proofs.V03EnergyIdentity

/-! The real third-jet calculation applies to the whole original penalized
functional. Its actual clock is fixed on every admissible spatial slice. -/

open scoped Topology ContDiff
open Metric Set Filter

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem penalizedFunctional_C3_of_actual_parts
    {d : VariationData X q} (hG : CotangentImmersion d.G) (j : ℕ)
    (F : VariationDisc X) (fz : ℂ → ℂ → CotangentPoint X.manifold)
    {r MA MB ML MT : ℝ} (ε : ℝ)
    (hSlices : ∀ z ∈ ball (0 : ℂ) r, AdmissibleVariationDisc d j {F with f := fz z})
    (hA : ContDiffOn ℝ 3 (fun z => spatialArea d (fz z)) (ball 0 r))
    (hB : ContDiffOn ℝ 3 (fun z => boundaryCost d j {F with f := fz z}) (ball 0 r))
    (hL : ContDiffOn ℝ 3 (fun z => (scalarDSq (logTrace d j (fz z))).toReal) (ball 0 r))
    (hT : ContDiffOn ℝ 3 (fun z => d.test (fz z 0) F.s) (ball 0 r))
    (hAb : ∀ z ∈ ball (0 : ℂ) r, ‖iteratedFDeriv ℝ 3 (fun w => spatialArea d (fz w)) z‖ ≤ MA)
    (hBb : ∀ z ∈ ball (0 : ℂ) r,
      ‖iteratedFDeriv ℝ 3 (fun w => boundaryCost d j {F with f := fz w}) z‖ ≤ MB)
    (hLb : ∀ z ∈ ball (0 : ℂ) r,
      ‖iteratedFDeriv ℝ 3 (fun w => (scalarDSq (logTrace d j (fz w))).toReal) z‖ ≤ ML)
    (hTb : ∀ z ∈ ball (0 : ℂ) r,
      ‖iteratedFDeriv ℝ 3 (fun w => d.test (fz w 0) F.s) z‖ ≤ MT) :
    ContDiffOn ℝ 3 (fun z => penalizedFunctional d j ε {F with f := fz z}) (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) r,
        ‖iteratedFDeriv ℝ 3 (fun w => penalizedFunctional d j ε {F with f := fz w}) z‖ ≤
          MB + |ε| * (MA + ML) + MT := by
  let J : ℂ → ℝ := fun z => boundaryCost d j {F with f := fz z} +
    ε * (spatialArea d (fz z) + (clockArea F).toReal +
      (scalarDSq (logTrace d j (fz z))).toReal) - d.test (fz z 0) F.s
  have heq : EqOn (fun z => penalizedFunctional d j ε {F with f := fz z}) J (ball 0 r) := by
    intro z hz
    dsimp only [penalizedFunctional]
    rw [variationEnergy_toReal_actual hG j (hSlices z hz).2.2.2.2.2.2.2.2]
    rfl
  have hc := linear_combination_C3_bound ε (clockArea F).toReal hA hB hL hT hAb hBb hLb hTb
  refine ⟨hc.1.congr heq, fun z hz => ?_⟩
  have hnear : (fun w => penalizedFunctional d j ε {F with f := fz w}) =ᶠ[𝓝 z] J := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact heq hw
  rw [(hnear.iteratedFDeriv (𝕜 := ℝ) 3).self_of_nhds]
  exact hc.2 z hz

end Yau.Blueprint.V02Proof
