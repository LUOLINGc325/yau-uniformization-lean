import Yau.LeafProofs.L16SpatialBootstrap

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem spatialWordDerivative_append {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (vs ws : List (Space n)) (g : Point n → V) :
    spatialWordDerivative (vs++ws) g = spatialWordDerivative vs (spatialWordDerivative ws g) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append,spatialWordDerivative,ih]

theorem c2_spatialSlice_contDiff {n : ℕ} {T t : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (ht : t ∈ Set.Icc 0 T) :
    ContDiff ℝ 2 (fun x : Space n => u (x,t)) :=
  contDiff_iff_contDiffAt.mpr (fun x => hu.2.2.2.2.1 (x,t) ⟨Set.mem_univ _,ht⟩)

/-- Genuine C2 spatial word fields imply the precise finite-order
regularity needed when commuting the next spatial derivatives. -/
theorem spatialSlice_contDiff_of_c2_words {n : ℕ} {T t : ℝ} {u : Point n → ℝ}
    (k : ℕ) (ht : t ∈ Set.Icc 0 T)
    (hWords : ∀ vs : List (Space n), vs.length ≤ k →
      C2 (cylinder Set.univ 0 T) (spatialWordDerivative vs u)) :
    ContDiff ℝ ((k+2 : ℕ) : ℕ∞ω) (fun x : Space n => u (x,t)) := by
  induction k generalizing u with
  | zero =>
    exact c2_spatialSlice_contDiff (hWords [] (by simp)) ht
  | succ k ih =>
    have hBase : C2 (cylinder Set.univ 0 T) u := hWords [] (by simp)
    have hDirections (e : Space n) :
        ContDiff ℝ ((k+2 : ℕ) : ℕ∞ω) (fun x : Space n => spatialPartial u e (x,t)) := by
      apply ih
      intro vs hvs
      have h := hWords (vs++[e]) (by simpa only [List.length_append,List.length_singleton] using Nat.add_le_add_right hvs 1)
      simpa only [spatialWordDerivative_append,spatialWordDerivative] using h
    have hOrder : (((k+2 : ℕ) : ℕ∞ω)+1) = ((k+1+2 : ℕ) : ℕ∞ω) := by
      simp only [Nat.cast_add,Nat.cast_ofNat]
      ac_rfl
    rw [← hOrder]
    apply contDiff_succ_iff_fderiv_apply.mpr
    exact ⟨(c2_spatialSlice_contDiff hBase ht).differentiable (by norm_num),
      (by simp),hDirections⟩

theorem spatialSlice_contDiff_infty_of_c2_words {n : ℕ} {T t : ℝ} {u : Point n → ℝ}
    (ht : t ∈ Set.Icc 0 T)
    (hWords : ∀ vs : List (Space n), C2 (cylinder Set.univ 0 T) (spatialWordDerivative vs u)) :
    ContDiff ℝ ∞ (fun x : Space n => u (x,t)) := by
  apply contDiff_infty.mpr
  intro k
  exact (spatialSlice_contDiff_of_c2_words k ht (fun vs _ => hWords vs)).of_le (by exact_mod_cast Nat.le_add_right k 2)

end Yau.LeafProofs.L16Aux
