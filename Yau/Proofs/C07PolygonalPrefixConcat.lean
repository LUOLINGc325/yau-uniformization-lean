import Yau.Proofs.C07CurveConcat
import Yau.Proofs.C07PolygonalPrefixConstant
import Mathlib.Topology.Homotopy.Basic

open scoped Manifold Topology unitInterval

noncomputable section

namespace Yau.Proofs.C07PolygonalPrefixAux

open Yau Set
open C07CurveConcatAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {A : Type*} [TopologicalSpace A]

/-- Concatenating two continuous families preserves joint continuity and
the original, exactly additive metric lengths. -/
theorem concat_families (x y z : C(A, M.Carrier))
    (γ : ∀ a, IntegrableCurve g (x a) (y a))
    (η : ∀ a, IntegrableCurve g (y a) (z a))
    (P Q : C(I × A, M.Carrier))
    (hP : ∀ u a, P (u, a) = (γ a).1 u)
    (hQ : ∀ u a, Q (u, a) = (η a).1 u) :
    ∃ (ζ : ∀ a, IntegrableCurve g (x a) (z a))
      (R : C(I × A, M.Carrier)),
      (∀ u a, R (u, a) = (ζ a).1 u) ∧
      (∀ a, curveLength g (ζ a).1 = curveLength g (γ a).1 + curveLength g (η a).1) ∧
      (∀ a u, (ζ a).1 u = concatPath (γ a).1 (η a).1 u) := by
  let F : ContinuousMap.Homotopy x y :=
    { toContinuousMap := P
      map_zero_left := fun a => (hP 0 a).trans (γ a).1.start_eq
      map_one_left := fun a => (hP 1 a).trans (γ a).1.finish_eq }
  let G : ContinuousMap.Homotopy y z :=
    { toContinuousMap := Q
      map_zero_left := fun a => (hQ 0 a).trans (η a).1.start_eq
      map_one_left := fun a => (hQ 1 a).trans (η a).1.finish_eq }
  let ζ : ∀ a, IntegrableCurve g (x a) (z a) := fun a =>
    ⟨concatPiecewise (γ a).1 (η a).1, (concat_integrable_length (γ a) (η a)).1⟩
  refine ⟨ζ, (F.trans G).toContinuousMap, ?_, ?_, fun _ _ => rfl⟩
  · intro u a
    rw [show (F.trans G).toContinuousMap (u, a) = (F.trans G) (u, a) from rfl,
      ContinuousMap.Homotopy.trans_apply]
    change _ = concatPath (γ a).1 (η a).1 u
    split_ifs with h
    · exact (hP _ a).trans (concatPath_left (γ a).1 (η a).1 h).symm
    · exact (hQ _ a).trans (if_neg h).symm
  · intro a
    exact (concat_integrable_length (γ a) (η a)).2

/-- A finite chain of jointly continuous integrable curve families can be
joined with one uniform length bound and one common image set. -/
theorem finite_concat (m : ℕ) (v : ℕ → C(A, M.Carrier)) (L : ℕ → ℝ)
    (K : Set M.Carrier) (B : Set A) (o : M.Carrier)
    (hvK : ∀ a, v 0 a ∈ K) (hvB : ∀ a ∈ B, v 0 a = o)
    (hseg : ∀ i < m,
      ∃ (γ : ∀ a, IntegrableCurve g (v i a) (v (i + 1) a))
        (P : C(I × A, M.Carrier)),
        (∀ u a, P (u, a) = (γ a).1 u) ∧
        (∀ a, curveLength g (γ a).1 ≤ L i) ∧
        (∀ a u, u ∈ Icc (0 : ℝ) 1 → (γ a).1 u ∈ K) ∧
        (∀ a ∈ B, ∀ u ∈ Icc (0 : ℝ) 1, (γ a).1 u = o)) :
    ∃ (γ : ∀ a, IntegrableCurve g (v 0 a) (v m a))
      (P : C(I × A, M.Carrier)),
      (∀ u a, P (u, a) = (γ a).1 u) ∧
      (∀ a, curveLength g (γ a).1 ≤ ∑ i ∈ Finset.range m, L i) ∧
      (∀ a u, u ∈ Icc (0 : ℝ) 1 → (γ a).1 u ∈ K) ∧
      (∀ a ∈ B, ∀ u ∈ Icc (0 : ℝ) 1, (γ a).1 u = o) := by
  induction m with
  | zero =>
    let P : C(I × A, M.Carrier) :=
      ⟨fun p => v 0 p.2, (v 0).continuous.comp continuous_snd⟩
    refine ⟨fun a => constantIntegrable g (v 0 a), P, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro a
      simp only [constant_length, Finset.range_zero, Finset.sum_empty, le_refl]
    · intro a u _
      exact hvK a
    · intro a ha u _
      exact hvB a ha
  | succ m ih =>
    obtain ⟨γ, P, hP, hγL, hγK, hγB⟩ :=
      ih (fun i hi => hseg i (Nat.lt_succ_of_lt hi))
    obtain ⟨η, Q, hQ, hηL, hηK, hηB⟩ := hseg m (Nat.lt_succ_self m)
    obtain ⟨ζ, R, hR, hlen, hζ⟩ := concat_families (v 0) (v m) (v (m + 1)) γ η P Q hP hQ
    refine ⟨ζ, R, hR, ?_, ?_, ?_⟩
    · intro a
      rw [hlen, Finset.sum_range_succ]
      exact add_le_add (hγL a) (hηL a)
    · intro a u hu
      rw [hζ, concatPath]
      split_ifs with h
      · exact hγK a (2 * u) ⟨by linarith [hu.1], by linarith⟩
      · exact hηK a (2 * u - 1) ⟨by linarith, by linarith [hu.2]⟩
    · intro a ha u hu
      rw [hζ, concatPath]
      split_ifs with h
      · exact hγB a ha (2 * u) ⟨by linarith [hu.1], by linarith⟩
      · exact hηB a ha (2 * u - 1) ⟨by linarith, by linarith [hu.2]⟩

end Yau.Proofs.C07PolygonalPrefixAux
