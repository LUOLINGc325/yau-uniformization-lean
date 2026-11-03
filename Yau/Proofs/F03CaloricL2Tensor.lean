import Yau.Proofs.F03CaloricCaccioppoli
import Yau.Proofs.F03CaloricPairNorm
import Yau.Proofs.F03CaloricRestriction
import Yau.Proofs.F03CaloricTensorBound
import Yau.Proofs.F03ClassicalCaloricWeakEquation

/-! Internally derived local L²-to-all-tensor estimates, before every solution. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

theorem classicalCaloric_compact_tensor_L2_bound
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (K : Set (Point d)) (hK : IsCompact K) (hKD : K ⊆ O ×ˢ Ioo l r) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Point d → ℝ,
      ContDiffOn ℝ ∞ v (O ×ˢ Ioo l r) →
      (∀ p ∈ O ×ˢ Ioo l r,linearOp (O ×ˢ Ioo l r) a b v p=0) →
      MemLp v 2 (volume.restrict (O ×ˢ Ioo l r)) → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m v p‖ ≤ C*(eLpNorm v 2 (volume.restrict (O ×ˢ Ioo l r))).toReal := by
  by_cases hKe : K=∅
  · refine ⟨1,zero_lt_one,?_⟩
    intro v _ _ _ p hp
    simpa only [hKe,mem_empty_iff_false] using hp
  obtain ⟨V,c,e,hV,hVc,hVO,hI,hCover⟩ := compact_subset_relcompact_cylinder hO hK hKD
  have hVD : V ×ˢ Ioo c e ⊆ O ×ˢ Ioo l r :=
    prod_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI)
  have hce : c < e := by
    obtain ⟨p,hp⟩ := Set.nonempty_iff_ne_empty.mpr hKe
    exact (hCover hp).2.1.trans (hCover hp).2.2
  let hABV : SmoothCoefficients (V ×ˢ Ioo c e) a b :=
    ⟨hAB.1.mono hVD,fun i => (hAB.2 i).mono hVD⟩
  let hEllV : Elliptic (V ×ˢ Ioo c e) a lam upper :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 p (hVD hp)⟩
  obtain ⟨W,hW,hKW,hWV,hWc⟩ := exists_open_between_and_isCompact_closure hK
    (hV.prod isOpen_Ioo) hCover
  let L : Set (Point d) := closure W
  have hLc : IsCompact L := hWc
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  letI : IsFiniteMeasure (volume.comap ((↑) : L → Point d)) :=
    comap_subtype_isFiniteMeasure_of_measure_lt_top volume L hLc.measurableSet hLc.measure_lt_top
  have hreg : L=closure (interior L) := by
    apply subset_antisymm
    · exact closure_mono hW.subset_interior_closure
    · exact closure_minimal interior_subset isClosed_closure
  obtain ⟨Ct,hCt,hTensor⟩ := caloricRepresentative_compact_tensor_bound hd V c e lam upper hV hce
    a b hABV hEllV L hLc hreg hWV m
  let Q : Set (Point d) := closure V ×ˢ Icc c e
  have hQc : IsCompact Q := hVc.prod isCompact_Icc
  have hQD : Q ⊆ O ×ˢ Ioo l r := prod_mono hVO hI
  obtain ⟨Ce,hCe,hEnergy⟩ := weak_caloric_compact_gradient_integral_bound O l r lam upper hO
    a b hAB hEll Q hQc hQD
  refine ⟨Ct*max 1 (Real.sqrt Ce),mul_pos hCt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)),?_⟩
  intro v hv hClass hu p hp
  obtain ⟨hE,hWE⟩ := classicalCaloricGradient_weak_energy O (Ioo l r) (hO.prod isOpen_Ioo)
    a b hAB v hv hClass
  obtain ⟨hvV,hGV⟩ := hE.2 V c e hV hVc hVO hI
  rw [productVolume_eq_restrict] at hvV hGV
  have hWGV : WeakGradient V (Ioo c e) v (classicalCaloricGradient v) :=
    weakGradient_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI) hE.1
  have hWEV : WeakEquation V (Ioo c e) a b (fun _ => 0) v (classicalCaloricGradient v) :=
    weakEquation_zero_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI) hWE
  let ev := caloricOfWeak V (Ioo c e) (hV.prod isOpen_Ioo) a b hABV v
    (classicalCaloricGradient v) hvV hGV hWGV hWEV
  have hPair : ‖ev‖ ≤ max 1 (Real.sqrt Ce)*(eLpNorm v 2 (volume.restrict (O ×ˢ Ioo l r))).toReal := by
    obtain ⟨hSum,hBound⟩ := hEnergy v (classicalCaloricGradient v) hE hWE hu
    change ‖((hvV.toLp v,fun i => (hGV i).toLp (fun p => classicalCaloricGradient v p i)) :
      CaloricAmbient (V ×ˢ Ioo c e))‖ ≤ _
    exact caloric_pair_norm_of_gradient_integral_bound (O ×ˢ Ioo l r) (V ×ˢ Ioo c e) Q hVD
      (prod_mono subset_closure Ioo_subset_Icc_self) v (classicalCaloricGradient v) hu hvV hGV
      hSum Ce hCe.le hBound
  have hRep := caloricRepresentative_eqOn_of_ae hd V c e lam upper hV hce a b hABV hEllV ev v
    (hv.continuousOn.mono hVD)
    (caloricOfWeak_value_ae V (Ioo c e) (hV.prod isOpen_Ioo) a b hABV v
      (classicalCaloricGradient v) hvV hGV hWGV hWEV)
  have hpL : p ∈ L := subset_closure (hKW hp)
  have hGerm : caloricRepresentative hd V c e lam upper hV hce a b hABV hEllV ev =ᶠ[𝓝 p] v := by
    filter_upwards [(hV.prod isOpen_Ioo).mem_nhds (hCover hp)] with q hq
    exact hRep hq
  rw [← (hGerm.iteratedFDeriv ℝ m).eq_of_nhds]
  exact (hTensor ev p hpL).trans ((mul_le_mul_of_nonneg_left hPair hCt.le).trans_eq (mul_assoc _ _ _).symm)

end Yau.Proofs.F03Aux
