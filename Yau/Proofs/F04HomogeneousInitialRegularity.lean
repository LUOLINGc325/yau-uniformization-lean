import Yau.Proofs.F04AuxiliaryExtension
import Yau.Proofs.F04ZeroPastJets
import Yau.Proofs.F04SmoothOperatorLinearity

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- The true coefficient extension and the true zero-past weak-energy
 bridge give initial-face smoothness for an ACTUAL homogeneous classical
 function with its compact linear growth. The coefficient extension is
 constructed internally; only the homogeneous remainder is zero-extended. -/
theorem homogeneous_linearGrowth_initial_regularization
    {n : ℕ} (hn : 0 < n) {O : Set (Space n)} (hO : IsOpen O)
    {S lam upper : ℝ} (hS : 0 < S)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hEll : Elliptic (O ×ˢ Icc 0 S) a lam upper)
    {u : Point n → ℝ} (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (hEq : ∀ p ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u p = 0)
    (hGrowth : ∀ W : Set (Space n), IsOpen W → IsCompact (closure W) → closure W ⊆ O →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ W, ∀ t ∈ Ioo 0 S, |u (x,t)| ≤ K*t)
    (V : Set (Space n)) (hV : IsOpen V) (hVC : IsCompact (closure V)) (hVO : closure V ⊆ O) :
    ∃ s : ℝ, 0 < s ∧ s < S ∧
      ContDiffOn ℝ ∞ (zeroPast u) (V ×ˢ Ioo (-s) s) ∧
      (∀ x ∈ V, ∀ m : ℕ, iteratedFDeriv ℝ m (zeroPast u) (x,0) = 0) ∧
      ∀ K : Set (Space n), IsCompact K → K ⊆ V → ∀ m : ℕ, ∀ η : ℝ, 0 < η →
        ∃ δ : ℝ, 0 < δ ∧ δ < s ∧ ∀ t ∈ Ioo 0 δ, ∀ x ∈ K,
          ‖iteratedFDeriv ℝ m u (x,t)‖ < η := by
  obtain ⟨W,hW,hVW,hWO,hWC⟩ := exists_open_between_and_isCompact_closure hVC hO hVO
  obtain ⟨ε,hε,ae,be,hse,hee,heq⟩ := auxiliaryCoefficientExtension n hn O W S lam upper
    hO hW hWC hWO hS a b hSmooth hEll
  have hWS : W ⊆ O := subset_closure.trans hWO
  have hR : 0 < S / 2 := half_pos hS
  have hRS : S / 2 < S := half_lt_self hS
  have hSub : W ×ˢ Icc (0 : ℝ) (S/2) ⊆ W ×ˢ Ioo (-ε) S := by
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], hp.2.2.trans_lt hRS⟩
  have hseR : SmoothCoefficients (W ×ˢ Icc 0 (S/2)) ae be :=
    ⟨hse.1.mono hSub, fun i => (hse.2 i).mono hSub⟩
  have hhu : ContDiffOn ℝ ∞ u (W ×ˢ Ioo 0 (S/2)) := hu.mono (fun p hp =>
    ⟨hWS hp.1,hp.2.1,hp.2.2.trans hRS⟩)
  have hPDE : ∀ p ∈ W ×ˢ Ioo 0 (S/2), linearOp (W ×ˢ Icc 0 (S/2)) ae be u p = 0 := by
    intro p hp
    have hm := heq p ⟨hp.1,hp.2.1.le,hp.2.2.trans hRS⟩
    calc
      _ = linearOp (W ×ˢ Icc 0 (S/2)) a b u p := by simp only [linearOp,hm.1,hm.2]
      _ = linearOp (O ×ˢ Icc 0 S) a b u p := linearOp_product_time_eq hp.1 (hWS hp.1)
        (Icc_mem_nhds hp.2.1 hp.2.2) (Icc_mem_nhds hp.2.1 (hp.2.2.trans hRS))
      _ = 0 := hEq p ⟨hWS hp.1,hp.2.1,hp.2.2.trans hRS⟩
  have hGrowthW : ∀ Z : Set (Space n), IsOpen Z → IsCompact (closure Z) → closure Z ⊆ W →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Z, ∀ t ∈ Ioo 0 (S/2), |u (x,t)| ≤ K*t := by
    intro Z hZ hZC hZW
    obtain ⟨K,hK,hKb⟩ := hGrowth Z hZ hZC (hZW.trans hWS)
    exact ⟨K,hK,fun x hx t ht => hKb x hx t ⟨ht.1,ht.2.trans hRS⟩⟩
  let s := min ε (S/2) / 2
  have hs : 0 < s := half_pos (lt_min hε hR)
  have hsε : s < ε := (half_lt_self (lt_min hε hR)).trans_le (min_le_left _ _)
  have hsR : s < S/2 := (half_lt_self (lt_min hε hR)).trans_le (min_le_right _ _)
  have hCross : V ×ˢ Ioo (-s) s ⊆ W ×ˢ Ioo (-ε) S := by
    intro p hp
    exact ⟨hVW (subset_closure hp.1),by linarith [hp.2.1],hp.2.2.trans (hsR.trans hRS)⟩
  obtain ⟨hSmoothZero,_hPDEZero⟩ := classical_homogeneous_zeroPast_smooth hn hW hseR
    (elliptic_mono hee hSub) hhu hPDE hGrowthW V s hV hVC hVW hs hsR
    ⟨hse.1.mono hCross,fun i => (hse.2 i).mono hCross⟩ (elliptic_mono hee hCross)
  refine ⟨s,hs,hsR.trans hRS,hSmoothZero,?_,?_⟩
  · intro x hx m
    exact zeroPast_initial_iteratedFDeriv hV hs hSmoothZero x hx m
  · intro K hK hKV m η hη
    exact zeroPast_uniform_compact_initial_jets hV hs hSmoothZero K hK hKV m hη

end Yau.F04Proof
