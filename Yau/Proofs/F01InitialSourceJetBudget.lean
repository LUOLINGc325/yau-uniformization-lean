import Yau.Proofs.F01InitialSourceGradient
import Yau.Proofs.F01PositiveMatrixCompactHolder

/-! Every fixed spatial jet of the actual differentiated potential
forcing has one Holder budget on a compact positive matrix range. The
constant is chosen before its coefficient fields and chart realization. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}
attribute [local instance] sourceMatrixDualNormed sourceSpatialMatrixNormed
  sourceMatrixDualSpace sourceSpatialMatrixSpace

local instance sourceGradientMatrixFinite (n : ℕ) :
    FiniteDimensional ℝ (Matrix (Fin n) (Fin n) ℂ) := by
  let J := frobeniusToComplexEntriesCLM (n := n)
  apply FiniteDimensional.of_injective J.toLinearMap
  intro H K h
  ext i j
  exact congrArg (fun A : Fin n → Fin n → ℂ => A i j) h

local instance sourceGradientSpatialMatrixFinite (n : ℕ) :
    FiniteDimensional ℝ (Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
  ContinuousLinearMap.finiteDimensional

local instance sourceGradientSpatialScalarFinite (n : ℕ) :
    FiniteDimensional ℝ (Space n →L[ℝ] ℝ) :=
  ContinuousLinearMap.finiteDimensional

local instance sourceGradientPairFinite (n : ℕ) :
    FiniteDimensional ℝ ((Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) × (Space n →L[ℝ] ℝ)) :=
  Module.Finite.prod

local instance sourceGradientInputFinite (n : ℕ) :
    FiniteDimensional ℝ (PotentialSourceInput n) :=
  Module.Finite.prod

local instance sourceGradientPairProper (n : ℕ) :
    ProperSpace ((Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) × (Space n →L[ℝ] ℝ)) :=
  @FiniteDimensional.proper ℝ inferInstance
    ((Space n →L[ℝ] Matrix (Fin n) (Fin n) ℂ) × (Space n →L[ℝ] ℝ))
    inferInstance inferInstance inferInstance (sourceGradientPairFinite n)

theorem potentialSourceGradient_jet_holder_budget {ell C : ℝ}
    (hell : 0 < ell) (hC : 0 ≤ C) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : Set (Point n)) (S : Set (Space n)) (β : ℝ)
      (Z : Point n → PotentialSourceInput n),
      IsOpen S → Q ⊆ S ×ˢ (Set.univ : Set ℝ) → HolderBound β Q Z C →
      (∀ p ∈ Q, ((Z p).1 - (ell : ℂ) • 1).PosSemidef) →
      (∀ p ∈ Q, ContDiffOn ℝ ∞ (fun z => Z (z, p.2)) S) →
      (∀ j : Fin (k + 1),
        HolderBound β Q (fun p => iteratedFDeriv ℝ j.val (fun z => Z (z, p.2)) p.1) C) →
      HolderBound β Q (fun p => iteratedFDeriv ℝ k
        (fun z => potentialSourceGradient (Z (z, p.2))) p.1) B := by
  let Hrange : Set (Matrix (Fin n) (Fin n) ℂ) :=
    closedBall 0 C ∩ {H | (H - (ell : ℂ) • 1).PosSemidef}
  let K : Set (PotentialSourceInput n) := Hrange ×ˢ closedBall 0 C
  have hClosed : IsClosed {H : Matrix (Fin n) (Fin n) ℂ |
      (H - (ell : ℂ) • 1).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)
  have hHrange : IsCompact Hrange := (isCompact_closedBall _ _).inter_right hClosed
  have hK : IsCompact K := hHrange.prod (isCompact_closedBall _ _)
  have hConv : Convex ℝ K := (positive_matrix_range_convex ell C).prod (convex_closedBall _ _)
  have hKU : K ⊆ potentialSourceDomain n := by
    intro p hp
    have hlo : ((ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)
    have hsum := hlo.add_posSemidef hp.1.2
    have he : (ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (p.1 - (ell : ℂ) • 1) = p.1 := by abel
    rw [he] at hsum
    exact (Complex.pos_iff.mp hsum.det_pos).1.ne'
  obtain ⟨B, hB, hb⟩ := @compact_iterated_jet_holder_composition_budget
    n (PotentialSourceInput n) (Space n →L[ℝ] ℝ)
    inferInstance inferInstance (sourceGradientInputFinite n)
    inferInstance inferInstance (sourceGradientSpatialScalarFinite n)
    K (potentialSourceDomain n) potentialSourceGradient C
    potentialSourceDomain_isOpen hK hConv hKU
    (potentialSourceGradient_contDiffOn n) hC k
  refine ⟨B, hB, ?_⟩
  intro Q S β Z hS hQS hZ hlo hs hj
  apply hb Q S β Z hS hQS ?_ hZ hs hj
  intro p hp
  have hNorm : max ‖(Z p).1‖ ‖(Z p).2‖ ≤ C := hZ.2.1 p hp
  exact ⟨⟨mem_closedBall.mpr (by simpa only [dist_zero_right] using (max_le_iff.mp hNorm).1),
      hlo p hp⟩, mem_closedBall.mpr (by simpa only [dist_zero_right] using (max_le_iff.mp hNorm).2)⟩

end Yau.NodeProofs.F01Aux
