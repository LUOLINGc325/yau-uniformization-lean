import Yau.Proofs.V03BoundaryMatrixVector
import Yau.Proofs.V03RealizedRawMultiplier
import Yau.Proofs.V03VelocityBounds
import Yau.Proofs.V03FrameSmooth
import Yau.Proofs.V03FrameEnergyBound
import Yau.Proofs.V03RectEntries

/-! One constant before every realization bounds the actual ambient
velocity's original boundary seminorm. All speed and scalar estimates are
derived from the original frame and realization predicates. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem ambientVelocity_uniform_boundaryDSq {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
      (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      RealizesFirstField d j a F E l h α fz R →
      boundaryDSq (fun θ b => ambientVelocity d F E l h α (circlePoint θ) b) ≤
        ENNReal.ofReal C * (1 + variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))) := by
  classical
  let k : ENNReal := ENNReal.ofReal (2 * L ^ 2)
  let A : ENNReal := ENNReal.ofReal (4 * (a : ℝ) ^ 2)
  let P : ENNReal := ENNReal.ofReal ((2 * Real.pi)⁻¹)
  let B : ENNReal := (q : ENNReal) * (Fintype.card (CotangentIndex n) : ENNReal) ^ 2
  let D : ENNReal := (q : ENNReal) * k * 2 * (1 + A) + 2 * B * (k * P + 2)
  have hD : D ≠ ⊤ := by dsimp only [D, B, k, P, A]; finiteness
  refine ⟨D.toReal, ENNReal.toReal_nonneg, fun F E l h α fz R hF hE hl hlL hR => ?_⟩
  let U : ℝ → Matrix (Fin q) (CotangentIndex n) ℂ :=
    fun θ => ambientFrame d.G F.f E (circlePoint θ)
  let lc : ℝ → CotangentIndex n → ℂ := fun θ => l (circlePoint θ)
  let c : ℝ → ℂ := fun θ => α (circlePoint θ) * h (circlePoint θ)
  have hUc (b : Fin q) (i : CotangentIndex n) : Continuous (fun θ => U θ b i) :=
    (ambientFrame_entry_contDiffOn hE.1 hd.2.2.2.2.1.1 b i).continuousOn.comp_continuous
      circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hUp (b : Fin q) (i : CotangentIndex n) : Function.Periodic (fun θ => U θ b i) (2 * Real.pi) :=
    circleTrace_periodic (fun ζ => ambientFrame d.G F.f E ζ b i)
  have hlc (i : CotangentIndex n) : Continuous (fun θ => lc θ i) :=
    (hl i).continuousOn.comp_continuous circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hlp (i : CotangentIndex n) : Function.Periodic (fun θ => lc θ i) (2 * Real.pi) :=
    circleTrace_periodic (fun ζ => l ζ i)
  have hln (θ : ℝ) : ‖(WithLp.toLp 2 (lc θ) : EuclideanSpace ℂ (CotangentIndex n))‖ ≤ L := by
    have hh : ‖(WithLp.toLp 2 (lc θ) : EuclideanSpace ℂ (CotangentIndex n))‖ ^ 2 ≤ L ^ 2 := by
      simpa only [EuclideanSpace.norm_sq_eq] using hlL (circlePoint θ) (circlePoint_mem_closedBall θ)
    nlinarith [norm_nonneg (WithLp.toLp 2 (lc θ) : EuclideanSpace ℂ (CotangentIndex n))]
  have hlentry (θ : ℝ) (i : CotangentIndex n) : ‖lc θ i‖ ≤ L :=
    (PiLp.norm_apply_le (WithLp.toLp 2 (lc θ) : EuclideanSpace ℂ (CotangentIndex n)) i).trans (hln θ)
  have hU1 (θ : ℝ) (b : Fin q) (i : CotangentIndex n) : ‖U θ b i‖ ≤ 1 :=
    normalized_matrix_entry_norm_le_one _ (hE.2.1 θ) b i
  have hWnorm (θ : ℝ) (b : Fin q) : ‖(U θ *ᵥ lc θ) b‖ ≤ L := by
    have hh := PiLp.norm_apply_le (WithLp.toLp 2 (U θ *ᵥ lc θ) : EuclideanSpace ℂ (Fin q)) b
    rw [euclidean_mulVec_norm_of_gram_eq_one _ (hE.2.1 θ)] at hh
    exact hh.trans (hln θ)
  have hWc (b : Fin q) : Continuous (fun θ => (U θ *ᵥ lc θ) b) := by
    change Continuous (fun θ => ∑ i, U θ b i * lc θ i)
    exact continuous_finsetSum _ (fun i _ => (hUc b i).mul (hlc i))
  have hWp (b : Fin q) : Function.Periodic (fun θ => (U θ *ᵥ lc θ) b) (2 * Real.pi) := by
    intro θ
    change (∑ i, U (θ + 2 * Real.pi) b i * lc (θ + 2 * Real.pi) i) = ∑ i, U θ b i * lc θ i
    exact Finset.sum_congr rfl (fun i _ => congrArg₂ (fun x y : ℂ => x * y) (hUp b i θ) (hlp i θ))
  have hcc : Continuous c := ((closedDisc_trace_contDiff hR.2.2.2.2.1).continuous).mul
    ((closedDisc_trace_contDiff hR.2.2.2.1).continuous)
  have hcp : Function.Periodic c (2 * Real.pi) := (circleTrace_periodic α).mul (circleTrace_periodic h)
  have hcn := realized_raw_multiplier_norm_le d hd j a F hF E l h α fz R hR
  have hcD := realized_raw_multiplier_boundaryDSq_le d hd j a F hF E l h α fz R hR
  norm_num only [ENNReal.ofReal_ofNat] at hcD
  have hW := boundaryDSq_matrix_mulVec_le hUc hlc hUp hlp hL hU1 hlentry
  have hUE := normalizedFrame_matrixDSq_le_energy hd j hE
  have hprod := boundaryDSq_vector_smul_le hcc hWc hcp hWp (by norm_num : (0 : ℝ) ≤ 1) hL hcn hWnorm
  norm_num only [one_pow, mul_one, ENNReal.ofReal_ofNat, Fintype.card_fin] at hprod hW
  let T : ENNReal := 1 + variationEnergy d j F + boundaryDSq lc
  have h1 : (1 : ENNReal) ≤ T := (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hEn : variationEnergy d j F ≤ T := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hlD : boundaryDSq lc ≤ T := le_add_left le_rfl
  change boundaryDSq (fun θ b => c θ * (U θ *ᵥ lc θ) b) ≤ ENNReal.ofReal D.toReal * T
  rw [ENNReal.ofReal_toReal hD]
  calc
    _ ≤ (q : ENNReal) * k * (2 * (1 + A * variationEnergy d j F)) +
        2 * (B * (k * (P * variationEnergy d j F) + 2 * boundaryDSq lc)) := by
      apply hprod.trans
      gcongr
      exact hW.trans (by gcongr)
    _ ≤ (q : ENNReal) * k * (2 * (T + A * T)) +
        2 * (B * (k * (P * T) + 2 * T)) := by
      gcongr
    _ = _ := by dsimp only [D]; ring

end Yau.Blueprint.V03Proof
