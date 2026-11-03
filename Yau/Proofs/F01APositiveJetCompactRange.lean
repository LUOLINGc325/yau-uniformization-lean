import Yau.Proofs.F01FiniteTaylorComposition
import Yau.Proofs.F01ScalarSymbolSmooth

/-! A bounded finite matrix jet with a fixed positive zeroth-order lower
bound lies in a compact subset of the genuine positive determinant domain.
The numerical bound of any continuous finite-jet expression is selected
before the jet, so it also applies uniformly to realized solution jets. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def matrixFiniteJetValue (k : ℕ)
    (p : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k) :
    Matrix (Fin n) (Fin n) ℂ := (p ⟨0, by omega⟩).curry0

theorem matrixFiniteJetValue_contDiff (k : ℕ) :
    ContDiff ℝ ∞ (matrixFiniteJetValue (n := n) k) := by
  letI jetGroups : (j : Fin (k + 1)) → NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
    fun j => ContinuousMultilinearMap.normedAddCommGroup'
  letI jetSpaces : (j : Fin (k + 1)) → NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
    fun j => ContinuousMultilinearMap.normedSpace'
  exact (continuousMultilinearCurryFin0 ℝ (Space n)
    (Matrix (Fin n) (Fin n) ℂ)).contDiff.comp
      (contDiff_apply ℝ (fun j : Fin (k + 1) => ContinuousMultilinearMap ℝ
        (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) ⟨0, by omega⟩)

theorem positive_matrix_finite_jet_expression_budget
    {F : Type*} [NormedAddCommGroup F] (k : ℕ) {ell R : ℝ}
    (hell : 0 < ell) (hR : 0 ≤ R)
    (Φ : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k → F)
    (hΦ : ContinuousOn Φ {p | 0 < (matrixFiniteJetValue k p).det.re}) :
    ∃ B : ℝ, 0 < B ∧ ∀ p : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k,
      (∀ j, ‖p j‖ ≤ R) →
      (matrixFiniteJetValue k p - (ell : ℂ) • 1).PosSemidef → ‖Φ p‖ ≤ B := by
  letI jetGroups : (j : Fin (k + 1)) → NormedAddCommGroup
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
    fun j => ContinuousMultilinearMap.normedAddCommGroup'
  letI jetSpaces : (j : Fin (k + 1)) → NormedSpace ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n) (Matrix (Fin n) (Fin n) ℂ)) :=
    fun j => ContinuousMultilinearMap.normedSpace'
  letI jetFinite : (j : Fin (k + 1)) → FiniteDimensional ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin j.val => Space n)
        (Matrix (Fin n) (Fin n) ℂ)) := fun j => continuousMultilinearMap_finiteDimensional j.val
  letI : FiniteDimensional ℝ (FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k) :=
    Module.Finite.pi (h := jetFinite)
  letI : ProperSpace (FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k) :=
    FiniteDimensional.proper ℝ _
  let K : Set (FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k) :=
    closedBall 0 R ∩ {p | (matrixFiniteJetValue k p - (ell : ℂ) • 1).PosSemidef}
  have hclosed : IsClosed {p : FiniteTaylorJet (Space n) (Matrix (Fin n) (Fin n) ℂ) k |
      (matrixFiniteJetValue k p - (ell : ℂ) • 1).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage
      ((matrixFiniteJetValue_contDiff k).continuous.sub continuous_const)
  have hK : IsCompact K := (isCompact_closedBall _ R).inter_right hclosed
  have hKU : K ⊆ {p | 0 < (matrixFiniteJetValue k p).det.re} := by
    intro p hp
    have hbase : ((ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)
    have hpos := hbase.add_posSemidef hp.2
    have he : (ell : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (matrixFiniteJetValue k p - (ell : ℂ) • 1) = matrixFiniteJetValue k p := by abel
    rw [he] at hpos
    exact (Complex.pos_iff.mp hpos.det_pos).1
  obtain ⟨B, hb⟩ := hK.exists_bound_of_continuousOn (hΦ.mono hKU)
  refine ⟨max 1 B + 1, by positivity, ?_⟩
  intro p hp hlo
  have hpK : p ∈ K := by
    refine ⟨?_, hlo⟩
    simpa only [mem_closedBall, dist_zero_right] using
      (pi_norm_le_iff_of_nonneg hR).mpr hp
  exact (hb p hpK).trans (by linarith [le_max_right (1 : ℝ) B])

end Yau.NodeProofs.F01Aux
