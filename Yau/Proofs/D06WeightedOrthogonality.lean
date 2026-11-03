import Yau.Proofs.D06AnalyticFactors

/-! The original weighted synthesis gives all Fourier orthogonality identities
for the same Hardy columns used by P. -/

open scoped ComplexOrder ComplexConjugate
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}
variable (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
variable (hLp : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
variable (hHerm : ∀ t, (L t).IsHermitian)
variable (m : ℝ) (hm : 0 < m)
variable (hLower : ∀ t, (L t - (m : ℂ) • 1).PosSemidef)
variable (M : ℝ) (hM : 0 ≤ M)
variable (hUpper : ∀ t, ((M : ℂ) • 1 - L t).PosSemidef)

theorem hardyFactorOperator_inner (a b : HardySeq r) :
    hardyWeightedInner L (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper a)
      (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper b) = inner ℂ a b := by
  letI : NormedAddCommGroup (WeightedHardySeq r) :=
    weightedHardyNormed L hLp hHerm m hm hLower
  letI : InnerProductSpace ℂ (WeightedHardySeq r) :=
    weightedHardyInnerProduct L hLp hHerm m hm hLower
  let U := weightedSynthesis L hLp hHerm m hm hLower M hM hUpper
  change inner ℂ (U a) (U b) = inner ℂ a b
  exact U.inner_map_map a b

theorem hardyFactorOperator_inner_single (n k : ℕ) (i j : Fin r) :
    hardyWeightedInner L
      (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper
        (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (n, i) 1))
      (hardyFactorOperator L hLp hHerm m hm hLower M hM hUpper
        (lp.single (E := fun _ : ℕ × Fin r => ℂ) 2 (k, j) 1)) =
      if (n, i) = (k, j) then 1 else 0 := by
  rw [hardyFactorOperator_inner, lp.inner_single_left]
  simp only [RCLike.inner_apply', map_one, one_mul, lp.single_apply, Pi.single_apply,
    eq_comm]

end Yau.NodeProofs.D06Aux
