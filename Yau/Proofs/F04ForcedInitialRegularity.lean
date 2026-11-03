import Yau.Proofs.F04HomogeneousInitialRegularity
import Yau.Proofs.F04LocalParticularExistence

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- Actual operator subtraction follows from actual smooth addition. -/
theorem linearOp_sub_of_smooth
    {n : ℕ} {O : Set (Space n)} {I : Set ℝ} (hO : IsOpen O) (hI : IsOpen I)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {u v : Point n → ℝ}
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ I)) (hv : ContDiffOn ℝ ∞ v (O ×ˢ I))
    {q : Point n} (hq : q ∈ O ×ˢ I) :
    linearOp (O ×ˢ I) a b (fun p => u p - v p) q =
      linearOp (O ×ˢ I) a b u q - linearOp (O ×ˢ I) a b v q := by
  have he := linearOp_add_of_smooth (a := a) (b := b) hO hI (hu.sub hv) hv hq
  simp only [sub_add_cancel] at he
  linarith only [he]

/-- A genuine forced classical solution with actual compact O(t) growth
 is smooth ONE-SIDED at its zero initial face. A genuine particular p is
 constructed, only u-p is extended and smoothed ACROSS zero, and p is
 added back on the original nonnegative time slab. No smoothness of the
 forced zero extension across zero is asserted or used. -/
theorem forced_linearGrowth_initial_regularization
    {n : ℕ} (hn : 0 < n) {O : Set (Space n)} (hO : IsOpen O)
    {S lam upper : ℝ} (hS : 0 < S)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f u : Point n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S))
    (hEll : Elliptic (O ×ˢ Icc 0 S) a lam upper)
    (hu : ContDiffOn ℝ ∞ u (O ×ˢ Ioo 0 S))
    (hEq : ∀ q ∈ O ×ˢ Ioo 0 S, linearOp (O ×ˢ Icc 0 S) a b u q = f q)
    (hGrowth : ∀ W : Set (Space n), IsOpen W → IsCompact (closure W) → closure W ⊆ O →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ W, ∀ t ∈ Ioo 0 S, |u (x,t)| ≤ K*t)
    (V : Set (Space n)) (hV : IsOpen V) (hVC : IsCompact (closure V)) (hVO : closure V ⊆ O) :
    ∃ s : ℝ, 0 < s ∧ s < S ∧ ContDiffOn ℝ ∞ (zeroPast u) (V ×ˢ Icc 0 s) := by
  obtain ⟨W,hW,hVW,hWO,hWC⟩ := exists_open_between_and_isCompact_closure hVC hO hVO
  have hWS : W ⊆ O := subset_closure.trans hWO
  obtain ⟨P,p,hP,hWP,_hPO,hp,hp0,_hpB,hpEq,hpGrowth⟩ :=
    local_zeroInitial_particular_exists hn hO (closure W) hWC hWO hS hSmooth hf hEll
  have hSW : SmoothCoefficients (W ×ˢ Icc 0 S) a b :=
    ⟨hSmooth.1.mono (prod_mono hWS (Subset.refl _)),
      fun i => (hSmooth.2 i).mono (prod_mono hWS (Subset.refl _))⟩
  have huW : ContDiffOn ℝ ∞ u (W ×ˢ Ioo 0 S) := hu.mono (prod_mono hWS (Subset.refl _))
  have hpW : ContDiffOn ℝ ∞ p (W ×ˢ Ioo 0 S) :=
    hp.mono (prod_mono (subset_univ _) Ioo_subset_Icc_self)
  let w : Point n → ℝ := fun q => u q - p q
  have hw : ContDiffOn ℝ ∞ w (W ×ˢ Ioo 0 S) := huW.sub hpW
  have hwEq : ∀ q ∈ W ×ˢ Ioo 0 S, linearOp (W ×ˢ Icc 0 S) a b w q = 0 := by
    intro q hq
    have hpPDE : linearOp (W ×ˢ Icc 0 S) a b p q = f q := by
      rw [linearOp_product_time_eq hq.1 (hWP (subset_closure hq.1))
        (Icc_mem_nhds hq.2.1 hq.2.2) (Icc_mem_nhds hq.2.1 hq.2.2)]
      exact hpEq q ⟨hWP (subset_closure hq.1),Ioo_subset_Icc_self hq.2⟩
    have huPDE : linearOp (W ×ˢ Icc 0 S) a b u q = f q := by
      rw [linearOp_product_time_eq hq.1 (hWS hq.1)
        (Icc_mem_nhds hq.2.1 hq.2.2) (Icc_mem_nhds hq.2.1 hq.2.2)]
      exact hEq q ⟨hWS hq.1,hq.2⟩
    have hSub := linearOp_sub_of_smooth (a := a) (b := b) hW isOpen_Ioo huW hpW hq
    have ht (v : Point n → ℝ) := linearOp_product_time_eq (u := v) (a := a) (b := b)
      hq.1 hq.1 (Icc_mem_nhds hq.2.1 hq.2.2) (isOpen_Ioo.mem_nhds hq.2)
    rw [← ht (fun q => u q - p q),← ht u,← ht p] at hSub
    change linearOp (W ×ˢ Icc 0 S) a b (fun q => u q - p q) q = 0
    rw [hSub,huPDE,hpPDE,sub_self]
  have hwGrowth : ∀ Z : Set (Space n), IsOpen Z → IsCompact (closure Z) → closure Z ⊆ W →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Z, ∀ t ∈ Ioo 0 S, |w (x,t)| ≤ K*t := by
    intro Z hZ hZC hZW
    obtain ⟨A,hA,hAb⟩ := hGrowth Z hZ hZC (hZW.trans hWS)
    obtain ⟨B,hB,hBb⟩ := hpGrowth (closure Z) hZC
    refine ⟨A+B,add_nonneg hA hB,?_⟩
    intro x hx t ht
    calc
      _ ≤ |u (x,t)| + |p (x,t)| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (u (x,t)) (p (x,t))
      _ ≤ A*t + B*t := add_le_add (hAb x hx t ht)
        (hBb x (subset_closure hx) t (Ioo_subset_Icc_self ht))
      _ = (A+B)*t := by ring
  obtain ⟨s,hs,hsS,hZero,_hJets,_hUniform⟩ := homogeneous_linearGrowth_initial_regularization hn hW hS
    hSW (elliptic_mono hEll (prod_mono hWS (Subset.refl _))) hw hwEq hwGrowth V hV hVC hVW
  have hs2 : 0 < s/2 := half_pos hs
  have hClosed : V ×ˢ Icc (0 : ℝ) (s/2) ⊆ V ×ˢ Ioo (-s) s := by
    intro q hq
    exact ⟨hq.1,by linarith [hq.2.1],hq.2.2.trans_lt (half_lt_self hs)⟩
  have hpClosed : ContDiffOn ℝ ∞ p (V ×ˢ Icc 0 (s/2)) := hp.mono (fun q hq =>
    ⟨mem_univ _,hq.2.1,hq.2.2.trans ((half_lt_self hs).trans hsS).le⟩)
  refine ⟨s/2,hs2,(half_lt_self hs).trans hsS,?_⟩
  apply ((hZero.mono hClosed).add hpClosed).congr
  intro q hq
  by_cases ht : 0 < q.2
  · rw [zeroPast_of_pos u ht,zeroPast_of_pos w ht]
    exact (sub_add_cancel (u q) (p q)).symm
  · have hq0 : q.2 = 0 := le_antisymm (le_of_not_gt ht) hq.2.1
    rw [zeroPast_of_nonpos u (le_of_not_gt ht),zeroPast_of_nonpos w (le_of_not_gt ht)]
    have hpq : p q = 0 := by simpa only [← hq0] using hp0 q.1
    rw [hpq,zero_add]

end Yau.F04Proof
