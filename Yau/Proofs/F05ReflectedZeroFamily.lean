import Yau.Proofs.F05CompactDirichletSolution
import Yau.Proofs.F05CompactFlowUniformBounds
import Yau.Proofs.F05SmoothFullJetHolder
import Yau.Proofs.F05FullJetHolderAlgebra
import Yau.Proofs.F05ManifoldTimeOperations
import Yau.Proofs.F05ManifoldFutureReflection
import Yau.Proofs.F05FixedTimeCutoffHolder
import Yau.Proofs.F05BootstrapUniformPatch

/-! Actual longer solutions with the proved common positive-time norm are
placed in one fixed homogeneous FTC cylinder. The datum is subtracted,
then time is shifted, a fixed cutoff creates the initial jets, and the
actual terminal reflection reaches the fixed endpoint. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ReflectedZeroField (s b τ : ℝ) (p w : M.Carrier → ℝ → ℝ) : M.Carrier → ℝ → ℝ :=
  F05ManifoldFutureReflection (τ-s)
    (F05ManifoldTimeCutoff (initialTimeCutoff b)
      (F05ManifoldTimeShift s (fun x t => w x t-p x t)))

theorem F05_reflected_zero_reconstruct {s b τ t : ℝ} (hb : 0 < b)
    (htτ : t ≤ τ) (htb : b/2 ≤ t-s) (p w : M.Carrier → ℝ → ℝ) (x : M.Carrier) :
    p x t+F05ReflectedZeroField s b τ p w x (t-s) = w x t := by
  have hPast : t-s ≤ τ-s := sub_le_sub_right htτ s
  simp only [F05ReflectedZeroField,F05ManifoldFutureReflection,hPast,ite_true,
    F05ManifoldTimeCutoff,F05ManifoldTimeShift,initialTimeCutoff_eq_one hb htb,
    one_mul,sub_add_cancel]
  ring

theorem F05_reflected_zero_family {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ)
    {T s b α C : ℝ} (hT : 0 < T) (hs : 0 < s) (hb : 0 < b) (hb1 : b ≤ 1)
    (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C) (hp : SmoothSpaceTime p (Icc 0 T))
    (τ : ℕ → ℝ) (w : ℕ → M.Carrier → ℝ → ℝ)
    (hτs : ∀ k, s < τ k) (hτT : ∀ k, τ k < T)
    (hBack : ∀ k, 0 ≤ 3*(τ k-s)-2*(T-s))
    (hw : ∀ k, F05CompactDirichletSolution O A h p (τ k) (w k))
    (hRelative : ∀ k i, F05RelSchauder α (F05D A i) (Icc s (τ k)) (pull A i (w k)) C) :
    ∃ K : ℝ, 0 < K ∧ ∀ k,
      (∀ i, C2 (F05Q A i (T-s)) (pull A i (F05ReflectedZeroField s b (τ k) p (w k)))) ∧
      (∀ i, HolderBound α (F05Q A i (T-s))
        (fun z => ((pull A i (F05ReflectedZeroField s b (τ k) p (w k)) z,
            spatialD (pull A i (F05ReflectedZeroField s b (τ k) p (w k))) z),
          (spatialDD (pull A i (F05ReflectedZeroField s b (τ k) p (w k))) z,
            timeD (F05Q A i (T-s)) (pull A i (F05ReflectedZeroField s b (τ k) p (w k))) z))) K) ∧
      (∀ x ∈ closure O, F05ReflectedZeroField s b (τ k) p (w k) x 0 = 0) ∧
      (∀ i z, z ∈ F05D A i →
        timeD (F05Q A i (T-s)) (pull A i (F05ReflectedZeroField s b (τ k) p (w k))) (z,0) = 0) ∧
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 (T-s), F05ReflectedZeroField s b (τ k) p (w k) x t = 0) := by
  obtain ⟨P,hP,hPBudget⟩ := F05_smooth_full_jet_holder_uniform hA p hT hp
  obtain ⟨E,hE,hθBudget⟩ := F05_fixed_time_cutoff_holder (n := n) hα hα1 hb hb1
  have hθ : ContDiff ℝ 1 (initialTimeCutoff b) := (initialTimeCutoff_contDiff b).of_le (by simp)
  have hθJet : deriv (initialTimeCutoff b) 0 = 0 := by
    simpa only [deriv_const] using (F05_initialTimeCutoff_zero_germ hb).deriv_eq
  let D := 4*E*(2*(C+P))
  let K := D*(38+12*(2:ℝ)^(α/2))
  have hK : 0 < K := by dsimp only [K,D]; positivity
  refine ⟨K,hK,?_⟩
  intro k
  have hτpos : 0 < τ k := hs.trans (hτs k)
  have hOld (i : Fin A.count) : C2 (F05Q A i (τ k)) (pull A i (w k)) := by
    obtain ⟨β,L,hβ,hβ1,hL,hSch,hCont,h0,hBoundary,hEq⟩ := hw k
    exact (hSch i).1
  have hOldBoundary (x : M.Carrier) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc 0 (τ k)) :
      w k x t = p x t := by
    obtain ⟨β,L,hβ,hβ1,hL,hSch,hCont,h0,hBoundary,hEq⟩ := hw k
    exact hBoundary x hx t ht
  have hOldLate (i : Fin A.count) : C2 (cylinder (F05D A i) s (τ k)) (pull A i (w k)) :=
    F05_c2_restrict_interval (hτs k) hs.le le_rfl (hOld i)
  have hPC2 (i : Fin A.count) : C2 (F05Q A i (τ k)) (pull A i p) :=
    F05_smooth_actual_chart_c2 hA hp hτpos (hτT k).le i
  have hPC2Late (i : Fin A.count) : C2 (cylinder (F05D A i) s (τ k)) (pull A i p) :=
    F05_c2_restrict_interval (hτs k) hs.le le_rfl (hPC2 i)
  let V := fun x t => w k x t-p x t
  have hDiffC2 (i : Fin A.count) : C2 (cylinder (F05D A i) s (τ k)) (pull A i V) :=
    c2_sub (hOldLate i) (hPC2Late i)
  have hDiffTuple (i : Fin A.count) : HolderBound α (cylinder (F05D A i) s (τ k))
      (fun z => ((pull A i V z,spatialD (pull A i V) z),
        (spatialDD (pull A i V) z,timeD (cylinder (F05D A i) s (τ k)) (pull A i V) z))) (C+P) := by
    have hW := F05_full_jet_holder_of_relative
      (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 2)) (hOldLate i) (hRelative k i)
    have hDatum := F05_full_jet_holder_restrict_interval (hτs k) hs.le le_rfl (hPC2 i)
      (hPBudget α hα hα1 (τ k) hτpos (hτT k).le i)
    exact F05_full_jet_holder_sub (hOldLate i) (hPC2Late i) hW hDatum
  have hDiffBoundary (x : M.Carrier) (hx : x ∈ frontier O) (t : ℝ) (ht : t ∈ Icc s (τ k)) : V x t = 0 := by
    dsimp only [V]
    rw [hOldBoundary x hx t ⟨hs.le.trans ht.1,ht.2⟩,sub_self]
  have hMap : MapsTo (fun t : ℝ => t+s) (Icc 0 (τ k-s)) (Icc s (τ k)) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hShift := F05_manifold_time_shift_jets A (sub_pos.mpr (hτs k)) hMap V
    hDiffC2 hDiffTuple hDiffBoundary
  have hCut := F05_manifold_time_cutoff_jets A (sub_pos.mpr (hτs k)) (F05ManifoldTimeShift s V)
    hShift.1 hShift.2.1 (initialTimeCutoff b) hθ (hθBudget (τ k-s)).1 (hθBudget (τ k-s)).2
    (initialTimeCutoff_initial b) hθJet hShift.2.2
  have hReflect := F05_manifold_future_reflection_jets hA (sub_pos.mpr (hτs k))
    (sub_lt_sub_right (hτT k) s) (hBack k) hα
    (F05ManifoldTimeCutoff (initialTimeCutoff b) (F05ManifoldTimeShift s V))
    hCut.1 hCut.2.1 (fun x _ => hCut.2.2.1 x) hCut.2.2.2.1 hCut.2.2.2.2
  exact hReflect

end Yau.Proofs.F05Aux
