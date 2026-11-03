import Yau.Proofs.V03LogCovectorBoundaryControl
import Yau.Proofs.V03BoundaryColumnField
import Yau.Proofs.V03BoundaryCovectorProduct
import Yau.Proofs.V03NormalizedVelocityScalar

/-! One constant before all realizations bounds the actual normalized
cleared logarithmic covector contraction in the original boundary seminorm. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem logFirstProduct_uniform_boundaryDSq {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      boundaryDSq (fun θ (_ : Unit) => normalizedVelocityScalar d j a F h α θ *
        (ambientLogCovector d j a (F.f (circlePoint θ)) ⬝ᵥ boundaryColumnField d F E l θ)) ≤
        ENNReal.ofReal C *
          (1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))) := by
  classical
  obtain ⟨Ca, Ma, hCa, hMa, hA⟩ := ambientLogCovector_uniform_boundary_control hd j a ha
  obtain ⟨Cw, hCw, hW⟩ := boundaryColumnField_uniform_boundaryDSq hd j L hL
  let N : ℝ := (q : ℝ) * Ma * L
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  let K : ENNReal := (q : ENNReal) *
    (ENNReal.ofReal (2 * L ^ 2) * ENNReal.ofReal Ca +
      ENNReal.ofReal (2 * Ma ^ 2) * ENNReal.ofReal Cw)
  let B : ENNReal := ENNReal.ofReal ((a : ℝ) ^ 2)
  let D : ENNReal := ENNReal.ofReal (2 * N ^ 2) * (2 * (1 + B)) + 2 * K
  have hD : D ≠ ⊤ := by dsimp only [D, K, B]; finiteness
  refine ⟨D.toReal, ENNReal.toReal_nonneg, fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  let A : ℝ → Fin q → ℂ := fun θ => ambientLogCovector d j a (F.f (circlePoint θ))
  let W := boundaryColumnField d F E l
  let c := normalizedVelocityScalar d j a F h α
  let u : ℝ → ℂ := fun θ => A θ ⬝ᵥ W θ
  let T : ENNReal := 1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))
  have h1 : (1 : ENNReal) ≤ T := (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hEn : variationEnergy d j F ≤ T := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hED : variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ)) ≤ T := by
    dsimp only [T]
    rw [add_assoc]
    exact le_add_left le_rfl
  have hAc (b : Fin q) : Continuous (fun θ => A θ b) :=
    cotangentCoefficient_trace_continuous hd
      (b := fun y => ambientLogCovector d j a y b)
      (fun x => ambientLogCovector_chart_entry_contDiffOn hd j a ha x b) hF
  have hAp (b : Fin q) : Function.Periodic (fun θ => A θ b) (2 * Real.pi) :=
    circleTrace_periodic (fun ζ => ambientLogCovector d j a (F.f ζ) b)
  have hWc := boundaryColumnField_continuous hd F E hE l hl
  have hWp := boundaryColumnField_periodic d F E l
  have hWn := boundaryColumnField_norm_le F E hE l hL hlL
  have hc : Continuous c := normalizedVelocityScalar_continuous hd j a F hF E l h α fz R hR
  have hcp := normalizedVelocityScalar_periodic d j a F h α
  have hcn : ∀ θ, ‖c θ‖ ≤ 1 :=
    realized_normalized_multiplier_norm_le d hd j a F hF E l h α fz R hR
  have huc : Continuous u := continuous_finsetSum _ (fun b _ => (hAc b).mul (hWc b))
  have hup : Function.Periodic u (2 * Real.pi) := by
    intro θ
    exact Finset.sum_congr rfl (fun b _ => congrArg₂ (· * ·) (hAp b θ) (hWp b θ))
  have hun (θ : ℝ) : ‖u θ‖ ≤ N := by
    simpa only [N, u, A, W, Fintype.card_fin] using
      dotProduct_norm_le_card_mul (fun b => (hA F hF).1 θ b) (fun b => hWn θ b) hMa
  have hdot := boundaryDSq_dotProduct_le hAc hWc hAp hWp hMa hL (hA F hF).1 hWn
  norm_num only [Fintype.card_fin] at hdot
  have hAD : boundaryDSq A ≤ ENNReal.ofReal Ca * T :=
    (hA F hF).2.trans (by gcongr)
  have hWD : boundaryDSq W ≤ ENNReal.ofReal Cw * T :=
    (hW F E l hE hl hlL).trans (by gcongr)
  have huD : boundaryDSq (fun θ (_ : Unit) => u θ) ≤ K * T := by
    calc
      _ ≤ (q : ENNReal) * (ENNReal.ofReal (2 * L ^ 2) * (ENNReal.ofReal Ca * T) +
          ENNReal.ofReal (2 * Ma ^ 2) * (ENNReal.ofReal Cw * T)) := by
        apply hdot.trans
        gcongr
      _ = _ := by dsimp only [K]; ring
  have hcD := realized_normalized_multiplier_boundaryDSq_le d hd j a F hF E l h α fz R hR
  norm_num only [ENNReal.ofReal_ofNat] at hcD
  have hcDT : boundaryDSq (fun θ (_ : Unit) => c θ) ≤ (2 * (1 + B)) * T := by
    calc
      _ ≤ 2 * (T + B * T) := by apply hcD.trans; gcongr
      _ = _ := by ring
  have hprod := boundaryDSq_mul_le (u := c) (v := u) hc huc hcp hup
    (by norm_num : (0 : ℝ) ≤ 1) hN hcn hun
  norm_num only [one_pow, mul_one, ENNReal.ofReal_ofNat] at hprod
  rw [ENNReal.ofReal_toReal hD]
  calc
    _ ≤ ENNReal.ofReal (2 * N ^ 2) * ((2 * (1 + B)) * T) + 2 * (K * T) := by
      apply hprod.trans
      gcongr
    _ = _ := by dsimp only [D]; ring

end Yau.Blueprint.V03Proof
