import Yau.Proofs.V03BoundaryMatrixVector
import Yau.Proofs.V03FrameSmooth
import Yau.Proofs.V03FrameEnergyBound
import Yau.Proofs.V03RectEntries
import Yau.Proofs.V03CirclePeriod

/-! The genuine normalized frame times the original holomorphic column
has uniform boundary bounds and seminorm control from the original energy. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def boundaryColumnField (d : VariationData X q) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ) (θ : ℝ) : Fin q → ℂ :=
  ambientFrame d.G F.f E (circlePoint θ) *ᵥ l (circlePoint θ)

theorem boundaryColumnField_periodic (d : VariationData X q) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ) (b : Fin q) :
    Function.Periodic (fun θ => boundaryColumnField d F E l θ b) (2 * Real.pi) :=
  circleTrace_periodic (fun ζ => (ambientFrame d.G F.f E ζ *ᵥ l ζ) b)

theorem boundaryColumnField_continuous {d : VariationData X q} (hd : VariationSetup d)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (hE : NormalizedDiscFrame d.G F.f E)
    (l : ℂ → CotangentIndex n → ℂ) (hl : HolomorphicColumn l) (b : Fin q) :
    Continuous (fun θ => boundaryColumnField d F E l θ b) := by
  change Continuous (fun θ => ∑ i, ambientFrame d.G F.f E (circlePoint θ) b i * l (circlePoint θ) i)
  apply continuous_finsetSum
  intro i _
  exact ((ambientFrame_entry_contDiffOn hE.1 hd.2.2.2.2.1.1 b i).continuousOn.comp_continuous
    circlePoint_contDiff.continuous circlePoint_mem_closedBall).mul
    ((hl i).continuousOn.comp_continuous circlePoint_contDiff.continuous circlePoint_mem_closedBall)

theorem boundaryColumnField_norm_le {d : VariationData X q} (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (hE : NormalizedDiscFrame d.G F.f E)
    (l : ℂ → CotangentIndex n → ℂ) {L : ℝ} (hL : 0 ≤ L)
    (hlL : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2)
    (θ : ℝ) (b : Fin q) : ‖boundaryColumnField d F E l θ b‖ ≤ L := by
  have hlNorm : ‖(WithLp.toLp 2 (l (circlePoint θ)) : EuclideanSpace ℂ (CotangentIndex n))‖ ≤ L := by
    have hs : ‖(WithLp.toLp 2 (l (circlePoint θ)) : EuclideanSpace ℂ (CotangentIndex n))‖ ^ 2 ≤ L ^ 2 := by
      simpa only [EuclideanSpace.norm_sq_eq] using hlL _ (circlePoint_mem_closedBall θ)
    nlinarith [norm_nonneg (WithLp.toLp 2 (l (circlePoint θ)) : EuclideanSpace ℂ (CotangentIndex n))]
  have hh := PiLp.norm_apply_le
    (WithLp.toLp 2 (boundaryColumnField d F E l θ) : EuclideanSpace ℂ (Fin q)) b
  rw [show boundaryColumnField d F E l θ = ambientFrame d.G F.f E (circlePoint θ) *ᵥ l (circlePoint θ)
      from rfl,
    euclidean_mulVec_norm_of_gram_eq_one _ (hE.2.1 θ)] at hh
  exact hh.trans hlNorm

theorem boundaryColumnField_uniform_boundaryDSq {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
      (l : ℂ → CotangentIndex n → ℂ),
      NormalizedDiscFrame d.G F.f E → HolomorphicColumn l →
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
      boundaryDSq (boundaryColumnField d F E l) ≤ ENNReal.ofReal C *
        (variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ))) := by
  let B : ENNReal := (q : ENNReal) * (Fintype.card (CotangentIndex n) : ENNReal) ^ 2
  let A : ENNReal := ENNReal.ofReal (2 * L ^ 2)
  let P : ENNReal := ENNReal.ofReal ((2 * Real.pi)⁻¹)
  let D : ENNReal := B * (A * P + 2)
  have hD : D ≠ ⊤ := by dsimp only [D, B, A, P]; finiteness
  refine ⟨D.toReal, ENNReal.toReal_nonneg, fun F E l hE hl hlL => ?_⟩
  have hU (b : Fin q) (i : CotangentIndex n) :
      Continuous (fun θ => ambientFrame d.G F.f E (circlePoint θ) b i) :=
    (ambientFrame_entry_contDiffOn hE.1 hd.2.2.2.2.1.1 b i).continuousOn.comp_continuous
      circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hlc (i : CotangentIndex n) : Continuous (fun θ => l (circlePoint θ) i) :=
    (hl i).continuousOn.comp_continuous
    circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hln (θ : ℝ) (i : CotangentIndex n) : ‖l (circlePoint θ) i‖ ≤ L := by
    have hs : ‖(WithLp.toLp 2 (l (circlePoint θ)) : EuclideanSpace ℂ (CotangentIndex n))‖ ^ 2 ≤ L ^ 2 := by
      simpa only [EuclideanSpace.norm_sq_eq] using hlL _ (circlePoint_mem_closedBall θ)
    have hn := PiLp.norm_apply_le
      (WithLp.toLp 2 (l (circlePoint θ)) : EuclideanSpace ℂ (CotangentIndex n)) i
    nlinarith [norm_nonneg (l (circlePoint θ) i),
      norm_nonneg (WithLp.toLp 2 (l (circlePoint θ)) : EuclideanSpace ℂ (CotangentIndex n))]
  have hb := boundaryDSq_matrix_mulVec_le
    (U := fun θ => ambientFrame d.G F.f E (circlePoint θ))
    (l := fun θ => l (circlePoint θ)) hU hlc
    (fun b i => circleTrace_periodic (fun ζ => ambientFrame d.G F.f E ζ b i))
    (fun i => circleTrace_periodic (fun ζ => l ζ i)) hL
    (fun θ b i => normalized_matrix_entry_norm_le_one _ (hE.2.1 θ) b i) hln
  have hframe := normalizedFrame_matrixDSq_le_energy hd j hE
  norm_num only [Fintype.card_fin] at hb
  rw [ENNReal.ofReal_toReal hD]
  calc
    _ ≤ B * (A * (P * variationEnergy d j F) + 2 * boundaryDSq (fun θ => l (circlePoint θ))) := by
      apply hb.trans
      gcongr
    _ ≤ B * (A * (P * (variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ)))) +
        2 * (variationEnergy d j F + boundaryDSq (fun θ => l (circlePoint θ)))) := by
      gcongr
      · exact le_add_right le_rfl
      · exact le_add_left le_rfl
    _ = _ := by dsimp only [D]; ring

end Yau.Blueprint.V03Proof
