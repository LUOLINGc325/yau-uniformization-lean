import Yau.Proofs.V03BoundaryAmbientTensor
import Yau.Proofs.V03BoundaryHilbertDifference

/-! A uniform estimate for the actual ambient tensor's full original
matrix Fourier seminorm in terms of the ambient and clock traces. -/

open scoped Topology ContDiff Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem boundaryAmbientTensor_uniform_matrixDSq {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : VariationDisc X, AdmissibleVariationDisc d j F →
      matrixDSq (boundaryAmbientTensor d j a F) ≤ ENNReal.ofReal C *
        (boundaryDSq (fun θ b => d.G (F.f (circlePoint θ)) b) +
          boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))) := by
  classical
  obtain ⟨C, M, hC, _, hbound⟩ := boundaryAmbientTensor_uniform_control hd j a ha
  let K : ℝ := 2 * C ^ 2 * (1 + (2 * d.T) ^ 2)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨(Fintype.card (Fin q × Fin q) : ℝ) * K, by positivity, fun F hF => ?_⟩
  have hU := admissible_ambient_trace_continuous hd hF
  have hw : Continuous (fun θ => F.w (circlePoint θ)) :=
    hF.2.1.continuousOn.comp_continuous circlePoint_contDiff.continuous circlePoint_mem_closedBall
  have hB := boundaryAmbientTensor_continuous hd j a ha hF
  have hBp := boundaryAmbientTensor_periodic d j a F
  have hT : 0 ≤ d.T := hd.1.le
  have hentry (b c : Fin q) : boundaryDSq (fun θ (_ : Unit) => boundaryAmbientTensor d j a F θ b c) ≤
      ENNReal.ofReal K * (boundaryDSq (fun θ k => d.G (F.f (circlePoint θ)) k) +
        boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))) := by
    apply boundaryDSq_le_of_hilbert_difference hU hw (hB.matrix_elem b c)
      (circleTrace_periodic (fun ζ => d.G (F.f ζ))) (circleTrace_periodic F.w)
      (fun θ => congrArg (fun A : Matrix (Fin q) (Fin q) ℂ => A b c) (hBp θ))
      hC (by positivity : 0 ≤ 2 * d.T)
    intro θ τ
    exact (hbound F hF).2 θ τ b c
  change boundaryDSq (fun θ (bc : Fin q × Fin q) => boundaryAmbientTensor d j a F θ bc.1 bc.2) ≤ _
  rw [boundaryDSq_eq_sum_singleton
    (fun θ (bc : Fin q × Fin q) => boundaryAmbientTensor d j a F θ bc.1 bc.2)]
  calc
    _ ≤ ∑ _bc : Fin q × Fin q, ENNReal.ofReal K *
        (boundaryDSq (fun θ k => d.G (F.f (circlePoint θ)) k) +
          boundaryDSq (fun θ (_ : Unit) => F.w (circlePoint θ))) :=
      Finset.sum_le_sum (fun bc _ => hentry bc.1 bc.2)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Fintype.card (Fin q × Fin q) : ℝ))]
      simp only [ENNReal.ofReal_natCast, mul_assoc]

end Yau.Blueprint.V03Proof
