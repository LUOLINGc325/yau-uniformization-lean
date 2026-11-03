import Yau.Proofs.V02WallTaylorCompactIncrementJets
import Yau.Proofs.V03GagliardoVector

/-! A finite Euclidean encoding of the actual parameter, outer phase and
coefficient vector, with its exact component-summed half-order energy. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V02WallTaylorProof
open Yau Yau.Blueprint V03Proof

abbrev IncrementAuxIndex (b : ℕ) := Unit ⊕ (Unit ⊕ Fin b)

def incrementAuxEncode {b : ℕ} (p : IncrementAux b) : EuclideanSpace ℂ (IncrementAuxIndex b) :=
  WithLp.toLp 2 (Sum.elim (fun _ => p.1) (Sum.elim (fun _ => p.2.1) p.2.2))

def incrementAuxDecode {b : ℕ} (p : EuclideanSpace ℂ (IncrementAuxIndex b)) : IncrementAux b :=
  (p (Sum.inl ()), (p (Sum.inr (Sum.inl ())), fun k => p (Sum.inr (Sum.inr k))))

theorem incrementAuxDecode_encode {b : ℕ} (p : IncrementAux b) :
    incrementAuxDecode (incrementAuxEncode p) = p := rfl

theorem incrementAuxEncode_decode {b : ℕ} (p : EuclideanSpace ℂ (IncrementAuxIndex b)) :
    incrementAuxEncode (incrementAuxDecode p) = p := by
  ext i
  rcases i with ⟨u⟩ | (⟨u⟩ | k) <;> rfl

theorem incrementAuxEncode_contDiff {b : ℕ} :
    ContDiff ℝ ∞ (incrementAuxEncode (b := b)) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro i
  rcases i with ⟨u⟩ | (⟨u⟩ | k)
  · exact contDiff_fst
  · exact contDiff_fst.comp contDiff_snd
  · exact (contDiff_apply ℝ (fun _ : Fin b => ℂ) k).comp (contDiff_snd.comp contDiff_snd)

theorem incrementAuxDecode_contDiff {b : ℕ} :
    ContDiff ℝ ∞ (incrementAuxDecode (b := b)) :=
  (contDiff_piLp_apply (p := 2) (i := Sum.inl ())).prodMk
    ((contDiff_piLp_apply (p := 2) (i := Sum.inr (Sum.inl ()))).prodMk
      (contDiff_pi.mpr (fun k => contDiff_piLp_apply (p := 2) (i := Sum.inr (Sum.inr k)))))

theorem boundaryDSq_const_value (z : ℂ) : boundaryDSq (fun (_ : ℝ) (_ : Unit) => z) = 0 := by
  have hb := boundaryDSq_le_of_difference_bound (u := fun _ => (0 : ℂ)) (v := fun _ => z)
    continuous_const continuous_const (fun _ => rfl) (fun _ => rfl) (C := 0) (by norm_num)
    (fun _ _ => by simp)
  have hb' : boundaryDSq (fun (_ : ℝ) (_ : Unit) => z) ≤ 0 := by
    simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero, zero_mul] using hb
  exact le_antisymm hb' zero_le

theorem boundaryDSq_incrementAuxEncode {b : ℕ} (p : ℝ → IncrementAux b) :
    boundaryDSq (fun θ i => incrementAuxEncode (p θ) i) =
      boundaryDSq (fun θ (_ : Unit) => (p θ).1) +
        boundaryDSq (fun θ (_ : Unit) => (p θ).2.1) + boundaryDSq (fun θ k => (p θ).2.2 k) := by
  simp only [boundaryDSq, Fintype.sum_sum_type, incrementAuxEncode, WithLp.ofLp_toLp,
    Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
  ring

theorem boundaryDSq_incrementAuxEncode_const_parameter {b : ℕ} (z : ℂ)
    (β : ℝ → ℂ) (c : ℝ → Fin b → ℂ) :
    boundaryDSq (fun θ i => incrementAuxEncode (z, (β θ, c θ)) i) =
      boundaryDSq (fun θ (_ : Unit) => β θ) + boundaryDSq c := by
  rw [boundaryDSq_incrementAuxEncode, boundaryDSq_const_value]
  simp only [zero_add]

end Yau.Blueprint.V02WallTaylorProof
