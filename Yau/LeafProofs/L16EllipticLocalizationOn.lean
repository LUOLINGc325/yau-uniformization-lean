import Yau.LeafProofs.L16ShortInverse

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- Frozen elliptic square roots require coefficient values only on the
    actual spatial set. An arbitrary exterior value is used solely for the
    existing algebraic choice theorem; no exterior regularity is asserted. -/
theorem elliptic_localization_equivs_on {n : ℕ} {α T lam upper : ℝ} {O : Set (Space n)}
    (hα : 0 ≤ α) (hT : 0 ≤ T) (hO : O.Nonempty) (a : Point n → Mat n)
    (hEll : Elliptic (cylinder O 0 T) a lam upper) (s : Finset (Space n))
    (hsO : ∀ c ∈ s, c ∈ O) :
    ∃ B : Space n → Space n ≃L[ℝ] Space n,
      (∀ c, constantHeatNormFactor α (B c) ≤ ellipticHeatNormBudget α lam upper) ∧
      constantHeatNormFactor α (ContinuousLinearEquiv.refl ℝ (Space n)) ≤ ellipticHeatNormBudget α lam upper ∧
      localizationGramIdentity s B (ContinuousLinearEquiv.refl ℝ (Space n)) a := by
  classical
  obtain ⟨x0,hx0⟩ := hO
  let aExt : Point n → Mat n := fun p => if p.1 ∈ O then a p else a (x0,p.2)
  have hEllExt : Elliptic (cylinder univ 0 T) aExt lam upper := by
    refine ⟨hEll.1,hEll.2.1,?_⟩
    intro p hp
    by_cases hx : p.1 ∈ O
    · simpa only [aExt,ite_eq_left hx] using hEll.2.2 p ⟨hx,hp.2⟩
    · simpa only [aExt,ite_eq_right hx] using hEll.2.2 (x0,p.2) ⟨hx0,hp.2⟩
  obtain ⟨B,hB,hId,hGram⟩ := elliptic_localization_equivs hα hT aExt hEllExt s
  refine ⟨B,hB,hId,?_⟩
  intro i hi H
  have h := hGram i hi H
  cases i with
  | none => simpa only [localizationFrozenMatrix] using h
  | some c =>
    have hc : c ∈ s := by simpa [localizationIndices] using hi
    simpa only [localizationFrozenMatrix,aExt,ite_eq_left (hsO c hc)] using h

end Yau.LeafProofs.L16Aux
