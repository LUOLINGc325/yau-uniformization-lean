import Yau.Proofs.V03LogTensorBoundaryControl
import Yau.Proofs.V03BoundaryColumnField
import Yau.Proofs.V03BoundaryQuadraticProduct
import Yau.Proofs.V03BoundaryCovectorProduct
import Yau.Proofs.V03NormalizedVelocityScalar

/-! The actual normalized cleared logarithmic quadratic contraction has
one uniform original boundary-seminorm bound before every realization. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem logMixedProduct_uniform_boundaryDSq {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      boundaryDSq (fun θ (_ : Unit) =>
        star (normalizedVelocityScalar d j a F h α θ) * normalizedVelocityScalar d j a F h α θ *
          (star (boundaryColumnField d F E l θ) ⬝ᵥ
            (ambientLogTensor d j a (F.f (circlePoint θ)) *ᵥ boundaryColumnField d F E l θ))) ≤
        ENNReal.ofReal C *
          (1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))) := by
  classical
  obtain ⟨Cb, Mb, hCb, hMb, hB⟩ := ambientLogTensor_uniform_boundary_control hd j a ha
  obtain ⟨Cw, hCw, hW⟩ := boundaryColumnField_uniform_boundaryDSq hd j L hL
  obtain ⟨Cq, hCq, hquad⟩ := boundaryDSq_quadratic_uniform (ι := Fin q) L Mb hL hMb
  let N : ℝ := (q : ℝ) * L * ((q : ℝ) * Mb * L)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  let K : ENNReal := ENNReal.ofReal Cq * (ENNReal.ofReal Cw + ENNReal.ofReal Cb)
  let A : ENNReal := ENNReal.ofReal ((a : ℝ) ^ 2)
  let D : ENNReal := ENNReal.ofReal (2 * N ^ 2) * (8 * (1 + A)) + 2 * K
  have hD : D ≠ ⊤ := by dsimp only [D, K, A]; finiteness
  refine ⟨D.toReal, ENNReal.toReal_nonneg, fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  let W := boundaryColumnField d F E l
  let B : ℝ → Matrix (Fin q) (Fin q) ℂ := fun θ => ambientLogTensor d j a (F.f (circlePoint θ))
  let c := normalizedVelocityScalar d j a F h α
  let c₂ : ℝ → ℂ := fun θ => star (c θ) * c θ
  let u : ℝ → ℂ := fun θ => star (W θ) ⬝ᵥ (B θ *ᵥ W θ)
  let T : ENNReal := 1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))
  have h1 : (1 : ENNReal) ≤ T := (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hEn : variationEnergy d j F ≤ T := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hED : variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ)) ≤ T := by
    dsimp only [T]
    rw [add_assoc]
    exact le_add_left le_rfl
  have hBc (b c : Fin q) : Continuous (fun θ => B θ b c) :=
    cotangentCoefficient_trace_continuous hd
      (b := fun y => ambientLogTensor d j a y b c)
      (fun x => ambientLogTensor_chart_entry_contDiffOn hd j a ha x b c) hF
  have hBp (b c : Fin q) : Function.Periodic (fun θ => B θ b c) (2 * Real.pi) :=
    circleTrace_periodic (fun ζ => ambientLogTensor d j a (F.f ζ) b c)
  have hWc := boundaryColumnField_continuous hd F E hE l hl
  have hWp := boundaryColumnField_periodic d F E l
  have hWn := boundaryColumnField_norm_le F E hE l hL hlL
  have hc : Continuous c := normalizedVelocityScalar_continuous hd j a F hF E l h α fz R hR
  have hcp := normalizedVelocityScalar_periodic d j a F h α
  have hcn : ∀ θ, ‖c θ‖ ≤ 1 :=
    realized_normalized_multiplier_norm_le d hd j a F hF E l h α fz R hR
  have hc₂ : Continuous c₂ := hc.star.mul hc
  have hcp₂ : Function.Periodic c₂ (2 * Real.pi) :=
    (show Function.Periodic (fun θ => star (c θ)) (2 * Real.pi) from fun θ => congrArg star (hcp θ)).mul hcp
  have hcn₂ (θ : ℝ) : ‖c₂ θ‖ ≤ 1 := by
    change ‖star (c θ) * c θ‖ ≤ 1
    rw [norm_mul, norm_star]
    nlinarith [hcn θ, norm_nonneg (c θ)]
  have huc : Continuous u := by
    change Continuous (fun θ => star (W θ) ⬝ᵥ (B θ *ᵥ W θ))
    simp_rw [quadraticForm_eq_sum]
    exact continuous_finsetSum _ (fun bc _ => ((hWc bc.1).star.mul (hBc bc.1 bc.2)).mul (hWc bc.2))
  have hup : Function.Periodic u (2 * Real.pi) := by
    intro θ
    change star (W (θ + 2 * Real.pi)) ⬝ᵥ (B (θ + 2 * Real.pi) *ᵥ W (θ + 2 * Real.pi)) =
      star (W θ) ⬝ᵥ (B θ *ᵥ W θ)
    simp only [quadraticForm_eq_sum]
    exact Finset.sum_congr rfl (fun bc _ =>
      congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg star (hWp bc.1 θ)) (hBp bc.1 bc.2 θ))
        (hWp bc.2 θ))
  have hun (θ : ℝ) : ‖u θ‖ ≤ N := by
    have hstar (b : Fin q) : ‖star (W θ) b‖ ≤ L := by
      simpa only [Pi.star_apply, norm_star] using hWn θ b
    have hbw (b : Fin q) : ‖(B θ *ᵥ W θ) b‖ ≤ (q : ℝ) * Mb * L := by
      change ‖∑ c, B θ b c * W θ c‖ ≤ (q : ℝ) * Mb * L
      simpa only [dotProduct, B, W, Fintype.card_fin] using
        dotProduct_norm_le_card_mul (fun c => (hB F hF).1 θ b c) (hWn θ) hMb
    simpa only [N, u, Fintype.card_fin] using dotProduct_norm_le_card_mul hstar hbw hL
  have hWD : boundaryDSq W ≤ ENNReal.ofReal Cw * T :=
    (hW F E l hE hl hlL).trans (by gcongr)
  have hBD : matrixDSq B ≤ ENNReal.ofReal Cb * T :=
    (hB F hF).2.trans (by gcongr)
  have huD : boundaryDSq (fun θ (_ : Unit) => u θ) ≤ K * T := by
    have hh := hquad W B hWc hBc hWp hBp hWn (hB F hF).1
    calc
      _ ≤ ENNReal.ofReal Cq * (ENNReal.ofReal Cw * T + ENNReal.ofReal Cb * T) := by
        apply hh.trans
        gcongr
      _ = _ := by dsimp only [K]; ring
  have hcD := normalizedVelocityScalar_sq_norm_boundaryDSq hd j a F hF E l h α fz R hR
  have hcDT : boundaryDSq (fun θ (_ : Unit) => c₂ θ) ≤ (8 * (1 + A)) * T := by
    calc
      _ ≤ 8 * (T + A * T) := by apply hcD.trans; gcongr
      _ = _ := by ring
  have hprod := boundaryDSq_mul_le (u := c₂) (v := u) hc₂ huc hcp₂ hup
    (by norm_num : (0 : ℝ) ≤ 1) hN hcn₂ hun
  norm_num only [one_pow, mul_one, ENNReal.ofReal_ofNat] at hprod
  rw [ENNReal.ofReal_toReal hD]
  calc
    _ ≤ ENNReal.ofReal (2 * N ^ 2) * ((8 * (1 + A)) * T) + 2 * (K * T) := by
      apply hprod.trans
      gcongr
    _ = _ := by dsimp only [D]; ring

end Yau.Blueprint.V03Proof
