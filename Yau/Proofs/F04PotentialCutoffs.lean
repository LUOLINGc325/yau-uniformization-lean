import Yau.Proofs.F04ExhaustionDomains

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- A GIVEN original controlled exhaustion produces actual monotone
 compact smooth source cutoffs, eventually EXACTLY one on each compact.
 The final dependency assembly must still produce that exhaustion from
 the exact registered P07 premise; F03 does not produce it. -/
theorem controlled_exhaustion_potential_cutoffs
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) :
    ∃ qs : ℕ → Pt X → ℝ,
      (∀ j, SmoothFn (qs j) ∧ HasCompactSupport (qs j) ∧ ∀ x, 0 ≤ qs j x ∧ qs j x ≤ 1) ∧
      (∀ x, Monotone (fun j => qs j x)) ∧
      ∀ K : Set (Pt X), IsCompact K → ∃ N : ℕ, ∀ j ≥ N, ∀ x ∈ K, qs j x = 1 := by
  let qs := fun j : ℕ => massCutoff u ((j : ℝ)+1)
  have hjPos (j : ℕ) : 0 < (j : ℝ)+1 := by positivity
  refine ⟨qs,?_,?_,?_⟩
  · intro j
    exact ⟨massCutoff_smooth hu.1 _,massCutoff_compact X o u hu (hjPos j),massCutoff_range u _⟩
  · intro x i j hij
    apply massCutoff_mono u (fun x => (show 0 ≤ u x from zero_le_one.trans (hu.2.2.1 x))) (hjPos i)
    have hcast : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    linarith
  · intro K hK
    obtain ⟨B,hB⟩ := (hK.image (Yau.LeafProofs.L18Aux.continuous_of_smoothFn hu.1)).bddAbove
    obtain ⟨N,hN⟩ := exists_nat_gt B
    refine ⟨N,?_⟩
    intro j hj x hx
    apply massCutoff_one u (hjPos j)
    have hxB : u x ≤ B := hB (mem_image_of_mem u hx)
    have hNj : (N : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hj
    linarith

end Yau.F04Proof
