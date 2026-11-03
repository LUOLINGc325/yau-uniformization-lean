import Yau.Proofs.F01JointRegularityIncrement
import Yau.Proofs.F01FiniteTaylorComposition

/-! A spatial jet tower with its actual clock equations bootstraps
to joint smoothness. The clock right-hand sides are specified smooth
finite-jet maps; no mixed time derivatives are assumed. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem joint_smooth_of_actual_finite_jet_clock_equations
    (f : E × ℝ → F) {W : Set (E × ℝ)} (hW : IsOpen W)
    (D : ∀ k : ℕ, Set ((E × ℝ) × FiniteTaylorJet E F (k + 2)))
    (Φ : ∀ k : ℕ, ((E × ℝ) × FiniteTaylorJet E F (k + 2)) →
      ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (hΦ : ∀ k, ContDiffOn ℝ ∞ (Φ k) (D k))
    (hMap : ∀ k p, p ∈ W →
      (p, fun j : Fin (k + 2 + 1) => iteratedFDeriv ℝ j.val (fun x => f (x, p.2)) p.1) ∈ D k)
    (hSlices : ∀ p ∈ W, ContDiffAt ℝ ∞ (fun x => f (x, p.2)) p.1)
    (hContinuous : ∀ k, ContinuousOn
      (fun p => iteratedFDeriv ℝ k (fun x => f (x, p.2)) p.1) W)
    (hClock : ∀ k p, p ∈ W → HasDerivAt
      (fun t => iteratedFDeriv ℝ k (fun x => f (x, t)) p.1)
      (Φ k (p, fun j : Fin (k + 2 + 1) => iteratedFDeriv ℝ j.val (fun x => f (x, p.2)) p.1)) p.2) :
    ContDiffOn ℝ ∞ f W ∧ ∀ k, ContDiffOn ℝ ∞
      (fun p => iteratedFDeriv ℝ k (fun x => f (x, p.2)) p.1) W := by
  have hSpace (k : ℕ) (p : E × ℝ) (hp : p ∈ W) :
      HasFDerivAt (fun y => iteratedFDeriv ℝ k (fun x => f (x, p.2)) y)
        ((iteratedFDeriv ℝ (k + 1) (fun x => f (x, p.2)) p.1).curryLeft) p.1 := by
    have hh := ((hSlices p hp).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).hasFDerivAt
    rw [fderiv_iteratedFDeriv] at hh
    change HasFDerivAt (fun y => iteratedFDeriv ℝ k (fun x => f (x, p.2)) y)
      ((iteratedFDeriv ℝ (k + 1) (fun x => f (x, p.2)) p.1).curryLeft) p.1 at hh
    exact hh
  have hAll (m : ℕ) : ∀ k, ContDiffOn ℝ (m : ℕ∞ω)
      (fun p => iteratedFDeriv ℝ k (fun x => f (x, p.2)) p.1) W := by
    induction m with
    | zero =>
      intro k
      exact contDiffOn_zero.mpr (hContinuous k)
    | succ m ih =>
      intro k
      letI innerJetGroup : NormedAddCommGroup
          (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :=
        ContinuousMultilinearMap.normedAddCommGroup'
      letI innerJetSpace : NormedSpace ℝ
          (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :=
        ContinuousMultilinearMap.normedSpace'
      letI outerJetGroup : NormedAddCommGroup
          (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :=
        ContinuousLinearMap.toNormedAddCommGroup
      letI outerJetSpace : NormedSpace ℝ
          (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :=
        ContinuousLinearMap.toNormedSpace
      let L : (ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F) →L[ℝ]
          (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) :=
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).toContinuousLinearEquiv.toContinuousLinearMap
      have hLeft : ContDiffOn ℝ (m : ℕ∞ω)
          (fun p => (iteratedFDeriv ℝ (k + 1) (fun x => f (x, p.2)) p.1).curryLeft) W :=
        L.contDiff.comp_contDiffOn (ih (k + 1))
      have hInputs : ContDiffOn ℝ (m : ℕ∞ω)
          (fun p : E × ℝ => (p, fun j : Fin (k + 2 + 1) =>
            iteratedFDeriv ℝ j.val (fun x => f (x, p.2)) p.1)) W :=
        contDiffOn_id.prodMk (contDiffOn_pi.mpr (fun j => ih j.val))
      have hRight : ContDiffOn ℝ (m : ℕ∞ω)
          (fun p => Φ k (p, fun j : Fin (k + 2 + 1) =>
            iteratedFDeriv ℝ j.val (fun x => f (x, p.2)) p.1)) W :=
        ((hΦ k).of_le (by simp)).comp hInputs (fun p hp => hMap k p hp)
      have hh := joint_contDiffOn_succ_of_space_time_partials
        (fun p => iteratedFDeriv ℝ k (fun x => f (x, p.2)) p.1)
        (fun p => (iteratedFDeriv ℝ (k + 1) (fun x => f (x, p.2)) p.1).curryLeft)
        (fun p => Φ k (p, fun j : Fin (k + 2 + 1) =>
          iteratedFDeriv ℝ j.val (fun x => f (x, p.2)) p.1)) hW m
        (hSpace k) (hClock k) hLeft hRight
      simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hSmooth (k : ℕ) : ContDiffOn ℝ ∞
      (fun p => iteratedFDeriv ℝ k (fun x => f (x, p.2)) p.1) W :=
    contDiffOn_infty.mpr (fun m => hAll m k)
  refine ⟨?_, hSmooth⟩
  have hh := (continuousMultilinearCurryFin0 ℝ E F).contDiff.comp_contDiffOn (hSmooth 0)
  exact hh

end Yau.NodeProofs.F01Aux
