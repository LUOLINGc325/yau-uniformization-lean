import Yau.Proofs.V03AmbientTensorBoundarySeminorm
import Yau.Proofs.V03MatrixBoundaryContraction
import Yau.Proofs.V03FrameSmooth
import Yau.Proofs.V03RectEntries

/-! One constant before every original admissible disc and normalized
frame controls the original symbol seminorm by their actual Fourier traces. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundarySymbol_eq_boundaryAmbientTensor {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a)
    (F : VariationDisc X) (hF : AdmissibleVariationDisc d j F)
    (E : ℂ → CotangentMatrix n) (θ : ℝ) :
    boundarySymbol d j a F E (circlePoint θ) =
      (ambientFrame d.G F.f E (circlePoint θ))ᴴ * boundaryAmbientTensor d j a F θ *
        ambientFrame d.G F.f E (circlePoint θ) := by
  have hy : F.f (circlePoint θ) ∈ cotangentSource (F.f (circlePoint θ)).1 :=
    mem_extChartAt_source _
  have ht := admissible_discTime_mem hF (circlePoint_mem_closedBall θ)
  rw [boundarySymbol_eq_fixedAmbientBoundaryTensor hd j a ha F hF E θ _ hy,
    fixedAmbientBoundaryTensor_eq_ambient hd j a ha _ hy
      ⟨ht.1.le, ht.2.le.trans hd.2.1.le⟩]
  rfl

theorem boundarySymbol_uniform_trace_bound {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
      matrixDSq (fun θ => boundarySymbol d j a F E (circlePoint θ)) ≤ ENNReal.ofReal C *
        (matrixDSq (fun θ => ambientFrame d.G F.f E (circlePoint θ)) +
          boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) +
            boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))) := by
  classical
  obtain ⟨_, M, _, hM, hbound⟩ := boundaryAmbientTensor_uniform_control hd j a ha
  obtain ⟨K, hK, hBK⟩ := boundaryAmbientTensor_uniform_matrixDSq hd j a ha
  let D : ENNReal := (Fintype.card (CotangentIndex n × CotangentIndex n) : ENNReal) *
    (Fintype.card (Fin q × Fin q) : ENNReal) ^ 2 * (3 * ENNReal.ofReal (2 * M ^ 2) + 4)
  have hD : D ≠ ⊤ := by dsimp only [D]; finiteness
  have hcoeff : ENNReal.ofReal (D.toReal * (1 + K)) = D * (1 + ENNReal.ofReal K) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hD,
      ENNReal.ofReal_add (by norm_num) hK, ENNReal.ofReal_one]
  refine ⟨D.toReal * (1 + K), mul_nonneg ENNReal.toReal_nonneg (by linarith), fun F E hF hE => ?_⟩
  let U : ℝ → Matrix (Fin q) (CotangentIndex n) ℂ :=
    fun θ => ambientFrame d.G F.f E (circlePoint θ)
  have hU (b : Fin q) (i : CotangentIndex n) : Continuous (fun θ => U θ b i) :=
    (ambientFrame_entry_contDiffOn hE.1 hd.2.2.2.2.1.1 b i).continuousOn.comp_continuous
      circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hUp (b : Fin q) (i : CotangentIndex n) : Function.Periodic (fun θ => U θ b i) (2 * Real.pi) :=
    circleTrace_periodic (fun ζ => ambientFrame d.G F.f E ζ b i)
  have hBc := boundaryAmbientTensor_continuous hd j a ha hF
  have hBp (b c : Fin q) : Function.Periodic (fun θ => boundaryAmbientTensor d j a F θ b c)
      (2 * Real.pi) := fun θ => congrArg (fun A : Matrix (Fin q) (Fin q) ℂ => A b c)
        (boundaryAmbientTensor_periodic d j a F θ)
  have hU1 (θ : ℝ) (b : Fin q) (i : CotangentIndex n) : ‖U θ b i‖ ≤ 1 :=
    normalized_matrix_entry_norm_le_one _ (hE.2.1 θ) b i
  have hh := matrixDSq_contraction_le hU (fun b c => hBc.matrix_elem b c) hUp hBp
    hM hU1 (hbound F hF).1
  have heq : (fun θ => boundarySymbol d j a F E (circlePoint θ)) =
      (fun θ => (U θ)ᴴ * boundaryAmbientTensor d j a F θ * U θ) := by
    funext θ
    exact boundarySymbol_eq_boundaryAmbientTensor hd j a ha F hF E θ
  rw [heq]
  change _ ≤ ENNReal.ofReal (D.toReal * (1 + K)) *
    (matrixDSq U + boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) +
      boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ)))
  calc
    _ ≤ D * (matrixDSq U + matrixDSq (boundaryAmbientTensor d j a F)) := hh
    _ ≤ D * (matrixDSq U + ENNReal.ofReal K *
        (boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) +
          boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ)))) := by
      gcongr
      exact hBK F hF
    _ ≤ D * ((1 + ENNReal.ofReal K) *
        (matrixDSq U + boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) +
          boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ)))) := by
      gcongr
      calc
        _ ≤ (1 + ENNReal.ofReal K) * matrixDSq U + (1 + ENNReal.ofReal K) *
            (boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) +
              boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))) := by
          apply add_le_add
          · calc
              _ = 1 * matrixDSq U := (one_mul _).symm
              _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (by positivity)
          · gcongr
            exact le_add_of_nonneg_left (by positivity)
        _ = _ := by ring
    _ = _ := by rw [hcoeff]; ring

end Yau.Blueprint.V03Proof
