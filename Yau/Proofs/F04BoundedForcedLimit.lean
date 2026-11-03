import Yau.Proofs.F03BoundedCaloricLimit
import Yau.Proofs.F04LocalParticularExistence
import Yau.Proofs.F04SmoothOperatorLinearity

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.Proofs.F03Aux Yau.LeafProofs.L16Aux

/-- An actual bounded classical forced sequence has a genuinely smooth
 pointwise limit near each compact spatial buffer. One particular solution
 is produced internally and subtracted BEFORE invoking the certified
 homogeneous classical limit theorem. No weak regularity oracle or new
 kernel/solver premise is supplied. -/
theorem bounded_classical_forced_limit_local
    {n : ℕ} (hn : 0 < n) {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (K : Set (Space n)) (hK : IsCompact K) (hKO : K ⊆ O)
    {S lam upper : ℝ} (hS : 0 < S)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f : Point n → ℝ}
    (hAB : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S)) (hEll : Elliptic (O ×ˢ Icc 0 S) a lam upper)
    (u : ℕ → Point n → ℝ) (v : Point n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (O ×ˢ Ioo 0 S))
    (hPDE : ∀ j p, p ∈ O ×ˢ Ioo 0 S → linearOp (O ×ˢ Icc 0 S) a b (u j) p = f p)
    (hBound : ∀ j p, p ∈ O ×ˢ Ioo 0 S → |u j p| ≤ B)
    (hPoint : ∀ p ∈ O ×ˢ Ioo 0 S, Tendsto (fun j => u j p) atTop (𝓝 (v p))) :
    ∃ V : Set (Space n), IsOpen V ∧ IsCompact (closure V) ∧ K ⊆ V ∧ closure V ⊆ O ∧
      ContDiffOn ℝ ∞ v (V ×ˢ Ioo 0 S) ∧
      ∀ p ∈ V ×ˢ Ioo 0 S, linearOp (V ×ˢ Icc 0 S) a b v p = f p := by
  obtain ⟨W,p,hW,hKW,hWO,hp,_hp0,hpB,hpPDE,_hpGrowth⟩ :=
    local_zeroInitial_particular_exists hn hO K hK hKO hS hAB hf hEll
  obtain ⟨V,hV,hKV,hVCW⟩ := hK.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hKW)
  have hVW : V ⊆ W := subset_closure.trans hVCW
  have hVCO : closure V ⊆ O := hVCW.trans hWO
  have hVO : V ⊆ O := subset_closure.trans hVCO
  have hVC : IsCompact (closure V) := hOC.of_isClosed_subset isClosed_closure (hVCO.trans subset_closure)
  have hU (j : ℕ) : ContDiffOn ℝ ∞ (u j) (V ×ˢ Ioo 0 S) :=
    (hu j).mono (Set.prod_mono hVO (Subset.refl _))
  have hP : ContDiffOn ℝ ∞ p (V ×ˢ Ioo 0 S) :=
    hp.mono (Set.prod_mono (subset_univ V) Ioo_subset_Icc_self)
  have hPEq (q : Point n) (hq : q ∈ V ×ˢ Ioo 0 S) : linearOp (V ×ˢ Ioo 0 S) a b p q = f q := by
    rw [linearOp_product_time_eq hq.1 (hVW hq.1) (Ioo_mem_nhds hq.2.1 hq.2.2) (Icc_mem_nhds hq.2.1 hq.2.2)]
    exact hpPDE q ⟨hVW hq.1,Ioo_subset_Icc_self hq.2⟩
  have hUEq (j : ℕ) (q : Point n) (hq : q ∈ V ×ˢ Ioo 0 S) :
      linearOp (V ×ˢ Ioo 0 S) a b (u j) q = f q := by
    rw [linearOp_product_time_eq hq.1 (hVO hq.1) (Ioo_mem_nhds hq.2.1 hq.2.2) (Icc_mem_nhds hq.2.1 hq.2.2)]
    exact hPDE j q ⟨hVO hq.1,hq.2⟩
  obtain ⟨Cp,hCp⟩ := hpB
  have hDiffBound : ∀ j q, q ∈ V ×ˢ Ioo 0 S → |u j q-p q| ≤ B+|Cp| := by
    intro j q hq
    calc
      _ ≤ |u j q|+|p q| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (u j q) (p q)
      _ ≤ B+|Cp| := add_le_add (hBound j q ⟨hVO hq.1,hq.2⟩)
        ((hCp q ⟨mem_univ _,Ioo_subset_Icc_self hq.2⟩).trans (le_abs_self Cp))
  have hDiffPDE : ∀ j q, q ∈ V ×ˢ Ioo 0 S →
      linearOp (V ×ˢ Ioo 0 S) a b (fun s => u j s-p s) q = 0 := by
    intro j q hq
    rw [local_linearOp_sub (hV.prod isOpen_Ioo) a b (hU j) hP hq,hUEq j q hq,hPEq q hq,sub_self]
  have hDiffPoint : ∀ q ∈ V ×ˢ Ioo 0 S,
      Tendsto (fun j => u j q-p q) atTop (𝓝 (v q-p q)) := by
    intro q hq
    exact (hPoint q ⟨hVO hq.1,hq.2⟩).sub tendsto_const_nhds
  obtain ⟨hDiff,hDiffEq,_hTensor,_hJets⟩ := bounded_classical_caloric_limit hn V 0 S lam upper hV hVC a b
    ⟨hAB.1.mono (Set.prod_mono hVO Ioo_subset_Icc_self),fun i => (hAB.2 i).mono (Set.prod_mono hVO Ioo_subset_Icc_self)⟩
    (elliptic_mono hEll (Set.prod_mono hVO Ioo_subset_Icc_self))
    (fun j q => u j q-p q) (fun q => v q-p q) (B+|Cp|) (add_nonneg hB (abs_nonneg Cp))
    (fun j => (hU j).sub hP) hDiffPDE hDiffBound hDiffPoint
  have hv : ContDiffOn ℝ ∞ v (V ×ˢ Ioo 0 S) :=
    (hDiff.add hP).congr (fun q _ => by ring)
  refine ⟨V,hV,hVC,hKV,hVCO,hv,?_⟩
  intro q hq
  have he := hDiffEq q hq
  rw [local_linearOp_sub (hV.prod isOpen_Ioo) a b hv hP hq,hPEq q hq] at he
  rw [linearOp_product_time_eq hq.1 hq.1 (Icc_mem_nhds hq.2.1 hq.2.2) (Ioo_mem_nhds hq.2.1 hq.2.2)]
  linarith

end Yau.F04Proof
