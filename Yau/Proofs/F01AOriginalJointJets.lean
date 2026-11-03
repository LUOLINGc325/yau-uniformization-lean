import Yau.Proofs.F01ANativeMixedClockEquations
import Yau.Proofs.F01ACompactLocalSchauder
import Yau.Proofs.F01ALocalInitialPotential

/-! Actual original-coordinate spatial estimates feed the native
mixed-clock recursion. The compact finite-jet range is constructed by that
recursion, and restriction to the closed spatial ball retains every face. -/
noncomputable section
open Set Metric
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem original_chart_closed_joint_budgets_of_spatial_bounds
    {ι : Type*} (g : HermitianField M) (hg : MetricSmooth g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {r T ell : ℝ} (hr : 0 < r) (hball : closedBall 0 (2 * r) ⊆ e.source)
    (hT : 0 < T) (hell : 0 < ell)
    (f : ι → Point n → ℝ) (C : ℕ → ℝ) (hC : ∀ k, 0 < C k)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 (2 * r) ×ˢ Icc 0 T))
    (hPDE : ∀ i z, z ∈ ball 0 (2 * r) → ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => f i (z,s))
        (localNativePotentialClock (pullbackMatrix g e) (f i) (z,t)) (Icc 0 T) t)
    (hLower : ∀ i p, p ∈ ball 0 (2 * r) ×ˢ Icc 0 T →
      (localNativePotentialMatrix (pullbackMatrix g e) (f i) p - (ell : ℂ) • 1).PosSemidef)
    (hSpatial : ∀ i k z, z ∈ ball 0 (2 * r) → ∀ t, t ∈ Icc 0 T →
      ‖iteratedFDeriv ℝ k (fun w => f i (w,t)) z‖ ≤ C k) :
    ∀ k, ∃ B : ℝ, 0 < B ∧ ∀ i p, p ∈ closedBall 0 r ×ˢ Icc 0 T →
      ‖iteratedFDerivWithin ℝ k (f i) (closedBall 0 r ×ˢ Icc 0 T) p‖ ≤ B := by
  let G : Space n → Matrix (Fin n) (Fin n) ℂ := pullbackMatrix g e
  let S : Point n → Matrix (Fin n) (Fin n) ℂ :=
    fun p => G p.1 - (p.2 : ℂ) • backgroundRicci G p.1
  let b : Point n → ℝ := fun p => -Real.log (G p.1).det.re
  let Ω : Set (Point n) := e.source ×ˢ univ
  let O : Set (Space n) := ball 0 (2 * r)
  let Q : Set (Point n) := closedBall 0 r ×ˢ Icc 0 T
  have hOe : O ⊆ e.source := ball_subset_closedBall.trans hball
  have hQO : Q ⊆ O ×ˢ Icc 0 T := by
    intro p hp
    exact ⟨(closedBall_subset_ball (by linarith : r < 2 * r)) hp.1, hp.2⟩
  obtain ⟨hG, hRic, hq⟩ := original_chart_background_smooth g hg e he hei
  have hS : ContDiffOn ℝ ∞ S Ω :=
    (hG.comp contDiffOn_fst (fun p hp => hp.1)).sub
      ((Complex.ofRealCLM.contDiff.comp_contDiffOn contDiffOn_snd).smul
        (hRic.comp contDiffOn_fst (fun p hp => hp.1)))
  have hb : ContDiffOn ℝ ∞ b Ω :=
    (hq.neg).comp contDiffOn_fst (fun p hp => hp.1)
  have hBase : O ×ˢ Icc 0 T ⊆ Ω := fun p hp => ⟨hOe hp.1, mem_univ _⟩
  have hPos : ∀ i p, p ∈ O ×ˢ Icc 0 T →
      0 < (S p + leviC (fun z => f i (z,p.2)) p.1).det.re := by
    intro i p hp
    have hh := (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)).add_posSemidef (hLower i p hp)
    have hpos : (localNativePotentialMatrix G (f i) p).PosDef := by
      simpa only [add_sub_cancel] using hh
    exact (Complex.pos_iff.mp hpos.det_pos).1
  have hEquation : ∀ i z, z ∈ O → ∀ t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => f i (z,s)) (localPotentialClockRHS S b (f i) (z,t))
        (Icc 0 T) t := by
    intro i z hz t ht
    convert hPDE i z hz t ht using 1
    simp only [localPotentialClockRHS, localNativePotentialClock,
      localNativePotentialMatrix, S, b, G, sub_eq_add_neg]
  have hUniqueQ : UniqueDiffOn ℝ Q := by
    have hballU : UniqueDiffOn ℝ (closedBall (0 : Space n) r) := by
      apply uniqueDiffOn_convex (convex_closedBall _ _)
      refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
      exact Filter.mem_of_superset (ball_mem_nhds 0 hr) ball_subset_closedBall
    exact hballU.prod (uniqueDiffOn_Icc hT)
  have hUniqueO : UniqueDiffOn ℝ (O ×ˢ Icc 0 T) := isOpen_ball.uniqueDiffOn.prod (uniqueDiffOn_Icc hT)
  intro k
  let R : ℝ := ∑ j : Fin (mixedClockJetOrder k 0 + 2 + 1), C j.val
  have hR : 0 ≤ R := Finset.sum_nonneg (fun j _ => (hC j.val).le)
  have hJets : ∀ i p, p ∈ Q → ∀ j : Fin (mixedClockJetOrder k 0 + 2 + 1),
      ‖iteratedFDeriv ℝ j.val (fun z => f i (z,p.2)) p.1‖ ≤ R := by
    intro i p hp j
    exact (hSpatial i j.val p.1 (hQO hp).1 p.2 hp.2).trans
      (Finset.single_le_sum (fun l _ => (hC l.val).le) (Finset.mem_univ j))
  obtain ⟨B, hB, hBound⟩ := local_uniform_joint_jet_budgets_of_spatial_bounds S b f
    isOpen_ball (convex_ball _ _) hT (e.open_source.prod isOpen_univ) hS hb hBase hf hPos hEquation
    k hQO ((isCompact_closedBall _ _).prod isCompact_Icc)
    (fun p hp => ⟨hOe (hQO hp).1, mem_univ _⟩) Subset.rfl hell hR hJets
    (fun i p hp => hLower i p (hQO hp))
  refine ⟨B, hB, ?_⟩
  intro i p hp
  rw [iteratedFDerivWithin_subset hQO hUniqueQ hUniqueO ((hf i).of_le (by simp)) hp]
  exact hBound i p hp

end Yau.NodeProofs.F01Aux
