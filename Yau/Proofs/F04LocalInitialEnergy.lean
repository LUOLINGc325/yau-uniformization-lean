import Yau.Proofs.F04InitialGradientEstimate
import Yau.Proofs.F04WeakRestriction

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

theorem local_initial_energy {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {S lam upper : ℝ} {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hsmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hell : Elliptic (O ×ˢ Icc 0 S) a lam upper) {u : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (heq : ∀ p ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u p = 0)
    (hGrowth : ∀ W : Set (Space n), IsOpen W → IsCompact (closure W) → closure W ⊆ O →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ W, ∀ t ∈ Ioo 0 S, |u (x, t)| ≤ K * t)
    (V : Set (Space n)) (s : ℝ) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVO : closure V ⊆ O) (hs : 0 < s) (hsS : s < S) :
    WeakGradient V (Ioo 0 s) u (dgGradient u) ∧
      MemLp u 2 (productVolume V (Ioo 0 s)) ∧
      (∀ i, MemLp (fun p => dgGradient u p i) 2 (productVolume V (Ioo 0 s))) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo 0 s, (∫ x in V, |u (x, t)| ^ 2) ≤ C) ∧
      InitialTrace V 0 u (fun _ => 0) ∧
      WeakEquation V (Ioo 0 s) a b (fun _ => 0) u (dgGradient u) := by
  obtain ⟨W, hW, hVW, hWO, hWc⟩ := exists_open_between_and_isCompact_closure hVc hO hVO
  obtain ⟨K, hK, hbound⟩ := hGrowth W hW hWc hWO
  have hVsub : V ⊆ O := fun x hx => hVO (subset_closure hx)
  have hVWsub : V ⊆ W := fun x hx => hVW (subset_closure hx)
  have hsub : V ×ˢ Ioo (0 : ℝ) s ⊆ O ×ˢ Ioo 0 S :=
    fun p hp => ⟨hVsub hp.1, hp.2.1, hp.2.2.trans hsS⟩
  have huV := hu.mono hsub
  have hvalues := initial_energy_value_and_trace hV hVc hVsub hs hsS.le hK hu
    (fun x hx t ht => hbound x (hVWsub hx) t ⟨ht.1, ht.2.trans hsS⟩)
  obtain ⟨C, _hC, hEstimate⟩ := initial_gradient_estimate hsmooth hell V W s
    hV hVc hVW hW hWc hWO hs hsS
  have hEnergy := hEstimate K hK u hu heq
    (fun x hx t ht => hbound x hx t ⟨ht.1, ht.2.trans hsS⟩)
  have hGrad (i : Yau.RIdx n) :
      MemLp (fun p => dgGradient u p i) 2 (productVolume V (Ioo 0 s)) := by
    have hg : AEStronglyMeasurable (fun p => dgGradient u p i) (productVolume V (Ioo 0 s)) := by
      rw [dg_productVolume_eq_restrict]
      exact (dgGradient_contDiffOn (hV.prod isOpen_Ioo) huV i).continuousOn.aestronglyMeasurable
        (hV.prod isOpen_Ioo).measurableSet
    apply (memLp_two_iff_integrable_sq hg).mpr
    apply hEnergy.1.mono' (hg.pow 2)
    apply Eventually.of_forall
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (dgGradient u p j)) (Finset.mem_univ i)
  refine ⟨classical_weakGradient (hV.prod isOpen_Ioo) huV,
    hvalues.1, hGrad, hvalues.2.1, hvalues.2.2, ?_⟩
  exact weak_homogeneous_equation_restrict hsub (homogeneous_weak_equation hO hsmooth hu heq)

end Yau.F04Proof
