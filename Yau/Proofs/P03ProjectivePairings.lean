import Yau.Proofs.P03SpanParameters

open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- Projective covector evaluation is genuinely differentiable in both the
spatial coordinates and the free projective coordinates. -/
theorem projectivePairing_differentiableOn (v : E → ComplexVector n)
    {U : Set E} (hU : IsOpen U) (hv : DifferentiableOn ℝ v U) (direction : Fin n) :
    DifferentiableOn ℝ (fun p : E × ({i : Fin n // i ≠ direction} → ℂ) =>
      coordinatePairing (projectiveCoordinates direction p.2) (v p.1)) (U ×ˢ univ) := by
  simp_rw [coordinatePairing_apply]
  intro p hp
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro k _
  have hq : DifferentiableAt ℝ
      (fun q : E × ({i : Fin n // i ≠ direction} → ℂ) =>
        projectiveCoordinates direction q.2 k) p :=
    ((differentiable_pi.mp (projectiveCoordinates_differentiable direction) k) p.2).comp p
      differentiableAt_snd
  have hx : DifferentiableAt ℝ
      (fun q : E × ({i : Fin n // i ≠ direction} → ℂ) => v q.1) p :=
    (hv.differentiableAt (hU.mem_nhds hp.1)).comp p differentiableAt_fst
  exact hq.mul ((differentiableAt_piLp 2).mp hx k)

def spanSchurCoefficients {L : ℕ} (W : E → Fin L → ComplexVector n) (direction : Fin n)
    (p : E × ({i : Fin n // i ≠ direction} → ℂ)) : Fin L → ℂ :=
  fun l => coordinatePairing (projectiveCoordinates direction p.2) (W p.1 l)

def spanSchurRightHand {m : ℕ} (V : E → Fin m → ComplexVector n) (direction : Fin n)
    (p : E × ({i : Fin n // i ≠ direction} → ℂ)) : Fin m → ℂ :=
  fun j => -coordinatePairing (projectiveCoordinates direction p.2) (V p.1 j)

theorem spanSchurCoefficients_differentiableOn {L : ℕ}
    (W : E → Fin L → ComplexVector n) {U : Set E} (hU : IsOpen U)
    (hW : ∀ l, DifferentiableOn ℝ (fun x => W x l) U) (direction : Fin n) (l : Fin L) :
    DifferentiableOn ℝ (fun p => spanSchurCoefficients W direction p l) (U ×ˢ univ) :=
  projectivePairing_differentiableOn (fun x => W x l) hU (hW l) direction

theorem spanSchurRightHand_differentiableOn {m : ℕ}
    (V : E → Fin m → ComplexVector n) {U : Set E} (hU : IsOpen U)
    (hV : ∀ j, DifferentiableOn ℝ (fun x => V x j) U) (direction : Fin n) (j : Fin m) :
    DifferentiableOn ℝ (fun p => spanSchurRightHand V direction p j) (U ×ˢ univ) :=
  (projectivePairing_differentiableOn (fun x => V x j) hU (hV j) direction).neg

end Yau.NodeProofs.P03Aux
