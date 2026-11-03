import Yau.Proofs.D06HardyFourier

/-! The original smooth periodic boundary matrix descends to the normalized
Haar circle, retaining its exact two Loewner bounds. -/

open scoped Matrix ComplexOrder ContDiff
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def periodicSymbol (L : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (hp : Function.Periodic L (2 * Real.pi)) : HardyCircle → Matrix (Fin r) (Fin r) ℂ :=
  hp.lift

@[simp] theorem periodicSymbol_coe (L : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (hp : Function.Periodic L (2 * Real.pi)) (t : ℝ) : periodicSymbol L hp t = L t :=
  hp.lift_coe t

theorem periodicSymbol_continuous (L : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (hp : Function.Periodic L (2 * Real.pi)) (hc : Continuous L) :
    Continuous (periodicSymbol L hp) := by
  unfold periodicSymbol Function.Periodic.lift
  apply hc.quotient_liftOn'

theorem periodicSymbol_continuous_of_smooth
    (L : ℝ → Matrix (Fin r) (Fin r) ℂ) (hp : Function.Periodic L (2 * Real.pi))
    (hs : ∀ i j, ContDiff ℝ ∞ (fun t => L t i j)) : Continuous (periodicSymbol L hp) := by
  apply periodicSymbol_continuous L hp
  exact continuous_pi fun i => continuous_pi fun j => (hs i j).continuous

theorem circleMatrix_entries_memLp_top
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (hc : Continuous L) (i j : Fin r) :
    MemLp (fun t => L t i j) ⊤ hardyCircleMeasure := by
  exact ContinuousMap.memLp (p := ⊤) (μ := hardyCircleMeasure) ℂ
    ⟨fun t => L t i j, (continuous_apply j).comp ((continuous_apply i).comp hc)⟩

theorem periodicSymbol_order
    (L : ℝ → Matrix (Fin r) (Fin r) ℂ) (hp : Function.Periodic L (2 * Real.pi))
    (m M : ℝ) (hord : ∀ t, (L t - (m : ℂ) • 1).PosSemidef ∧
      ((M : ℂ) • 1 - L t).PosSemidef) :
    ∀ t : HardyCircle, (periodicSymbol L hp t - (m : ℂ) • 1).PosSemidef ∧
      ((M : ℂ) • 1 - periodicSymbol L hp t).PosSemidef := by
  intro t
  induction t using Quotient.inductionOn with
  | h t => simpa only [periodicSymbol_coe] using hord t

theorem hermitian_of_scalar_lower (A : Matrix (Fin r) (Fin r) ℂ) (m : ℝ)
    (hA : (A - (m : ℂ) • 1).PosSemidef) : A.IsHermitian := by
  have hscalar : ((m : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)).IsHermitian :=
    Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint])
  simpa only [sub_add_cancel] using hA.isHermitian.add hscalar

end Yau.NodeProofs.D06Aux
