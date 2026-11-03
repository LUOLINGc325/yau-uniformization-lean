import Yau.Proofs.F04LocalParticularExistence
import Yau.Proofs.F04CompactCylinderL2
import Yau.Proofs.F04ForcedWeakEquation
import Yau.Proofs.F04SmoothLocalEnergy
import Yau.Proofs.F04WeakLinearCombination
import Yau.Proofs.F04CompactWeakFields
import Yau.Proofs.F04SmoothOperatorLinearity
import Yau.LeafProofs.L16InteriorSmoothing

open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

/-- Genuine forced weak interior regularity. An actual zero-initial
 particular solution is constructed, its actual weak equation subtracted,
 and the proved homogeneous interior theorem applied to the remainder.
 No regularity or homogeneous-remainder premise is supplied. The forced
 solution is never extended by zero. -/
theorem forced_weak_interior_regularization
    {n : ℕ} (hn : 0 < n) {O V : Set (Space n)}
    (hO : IsOpen O) (hV : IsOpen V) (hVC : IsCompact (closure V)) (hVO : closure V ⊆ O)
    {S lam upper : ℝ} (hS : 0 < S)
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {f u : Point n → ℝ}
    {G : Point n → RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Icc 0 S) a b)
    (hf : ContDiffOn ℝ ∞ f (O ×ˢ Icc 0 S))
    (hEll : Elliptic (O ×ˢ Icc 0 S) a lam upper)
    (huL : MemLp u 2 (productVolume V (Ioo 0 S)))
    (hGL : ∀ i, MemLp (fun q => G q i) 2 (productVolume V (Ioo 0 S)))
    (huE : LocalEnergy V (Ioo 0 S) u G)
    (huEq : WeakEquation V (Ioo 0 S) a b f u G) :
    ∃ (v p w : Point n → ℝ),
      ContDiffOn ℝ ∞ v (V ×ˢ Ioo 0 S) ∧
      u =ᵐ[productVolume V (Ioo 0 S)] v ∧
      (∀ q ∈ V ×ˢ Ioo 0 S, linearOp (V ×ˢ Icc 0 S) a b v q = f q) ∧
      ContDiffOn ℝ ∞ p (univ ×ˢ Icc 0 S) ∧ (∀ x, p (x,0) = 0) ∧
      (∀ L : Set (Space n), IsCompact L →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ L, ∀ t ∈ Icc 0 S, |p (x,t)| ≤ C*t) ∧
      ContDiffOn ℝ ∞ w (V ×ˢ Ioo 0 S) ∧
      (∀ q ∈ V ×ˢ Ioo 0 S, linearOp (V ×ˢ Ioo 0 S) a b w q = 0) ∧
      (∀ q, v q = w q + p q) := by
  obtain ⟨W,p,hW,hKW,hWO,hp,hp0,_hpB,hpEq,hpGrowth⟩ :=
    local_zeroInitial_particular_exists hn hO (closure V) hVC hVO hS hSmooth hf hEll
  have hVSub : V ⊆ O := subset_closure.trans hVO
  have hVClosed : V ×ˢ Icc (0 : ℝ) S ⊆ O ×ˢ Icc 0 S := prod_mono hVSub (Subset.refl _)
  have hVOpen : V ×ˢ Ioo (0 : ℝ) S ⊆ O ×ˢ Icc 0 S := prod_mono hVSub Ioo_subset_Icc_self
  have hSV : SmoothCoefficients (V ×ˢ Icc 0 S) a b :=
    ⟨hSmooth.1.mono hVClosed, fun i => (hSmooth.2 i).mono hVClosed⟩
  have hpS : ContDiffOn ℝ ∞ p (V ×ˢ Ioo 0 S) :=
    hp.mono (prod_mono (subset_univ _) Ioo_subset_Icc_self)
  have hpPDE : ∀ q ∈ V ×ˢ Ioo 0 S, linearOp (V ×ˢ Icc 0 S) a b p q = f q := by
    intro q hq
    rw [linearOp_product_time_eq hq.1 (hKW (subset_closure hq.1))
      (Icc_mem_nhds hq.2.1 hq.2.2) (Icc_mem_nhds hq.2.1 hq.2.2)]
    exact hpEq q ⟨hKW (subset_closure hq.1), Ioo_subset_Icc_self hq.2⟩
  have hpWE := forced_classical_weakEquation hV hSV hpS (hf.mono hVOpen) hpPDE
  have hpE := smooth_localEnergy hV isOpen_Ioo hpS
  obtain ⟨hpL,hpGL⟩ := fullSpace_smooth_compactCylinder_memLp_gradient hV hVC hp
  have hpGL' : ∀ i, MemLp (fun q => dgGradient p q i) 2 (productVolume V (Ioo 0 S)) := hpGL
  obtain ⟨hPu,hRu⟩ := compact_buffer_weak_fields_memLp hO hV hVC hVO hS le_rfl hSmooth hGL
  obtain ⟨hPp,hRp⟩ := compact_buffer_weak_fields_memLp hO hV hVC hVO hS le_rfl hSmooth hpGL'
  have hremE := localEnergy_sub_of_memLp huL hpL hGL hpGL' huE hpE
  have hremWE := weakEquation_sub_same_source huL hpL hPu hPp hRu hRp huEq hpWE
  have hSVOpen : SmoothCoefficients (V ×ˢ Ioo 0 S) a b :=
    ⟨hSmooth.1.mono hVOpen, fun i => (hSmooth.2 i).mono hVOpen⟩
  obtain ⟨w,hw,hwAE,hwEq⟩ := Yau.LeafProofs.L16Interior.homogeneousInteriorSmoothing
    n hn V 0 S lam upper hV hS a b (fun q => u q - p q)
    (fun q i => G q i - dgGradient p q i) hSVOpen
    (elliptic_mono hEll hVOpen) hremE hremWE
  refine ⟨fun q => w q + p q,p,w,hw.add hpS,?_,?_,hp,hp0,hpGrowth,hw,hwEq,fun _ => rfl⟩
  · filter_upwards [hwAE] with q hq
    linarith only [hq]
  · intro q hq
    rw [linearOp_product_time_eq hq.1 hq.1
      (Icc_mem_nhds hq.2.1 hq.2.2) (isOpen_Ioo.mem_nhds hq.2),
      linearOp_add_of_smooth hV isOpen_Ioo hw hpS hq, hwEq q hq]
    rw [← linearOp_product_time_eq hq.1 hq.1
      (Icc_mem_nhds hq.2.1 hq.2.2) (isOpen_Ioo.mem_nhds hq.2)]
    simpa only [zero_add] using hpPDE q hq

end Yau.F04Proof
