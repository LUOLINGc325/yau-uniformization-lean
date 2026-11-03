import Yau.Proofs.F03CaloricCaccioppoli
import Yau.Proofs.F03CaloricPairDifference
import Yau.Proofs.F03CaloricRestriction

/-! Applying the actual compact energy estimate to differences gives a Cauchy graph. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000

theorem classicalCaloric_inner_pair_cauchy
    (O V : Set (Space d)) (l r c e lam upper : ℝ) (hO : IsOpen O) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O) (hI : Icc c e ⊆ Ioo l r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (u : ℕ → Point d → ℝ) (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (O ×ˢ Ioo l r))
    (hClass : ∀ j p,p ∈ O ×ˢ Ioo l r → linearOp (O ×ˢ Ioo l r) a b (u j) p=0)
    (hf : ∀ j, MemLp (u j) 2 (volume.restrict (O ×ˢ Ioo l r)))
    (hCauchy : CauchySeq (fun j => (hf j).toLp (u j))) :
    ∃ ev : ℕ → CaloricSpace (V ×ˢ Ioo c e) (hV.prod isOpen_Ioo) a b
      ⟨hAB.1.mono (prod_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI)),
        fun i => (hAB.2 i).mono (prod_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI))⟩,
      CauchySeq ev ∧ ∀ j, (ev j).val.1 =ᵐ[volume.restrict (V ×ˢ Ioo c e)] u j := by
  let D := O ×ˢ Ioo l r
  let Q := closure V ×ˢ Icc c e
  have hD : IsOpen D := hO.prod isOpen_Ioo
  have hVD : V ×ˢ Ioo c e ⊆ D := prod_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI)
  have hQc : IsCompact Q := hVc.prod isCompact_Icc
  have hQD : Q ⊆ D := prod_mono hVO hI
  let hABV : SmoothCoefficients (V ×ˢ Ioo c e) a b :=
    ⟨hAB.1.mono hVD,fun i => (hAB.2 i).mono hVD⟩
  have hEnergy : ∀ j, LocalEnergy O (Ioo l r) (u j) (classicalCaloricGradient (u j)) :=
    fun j => (classicalCaloricGradient_weak_energy O (Ioo l r) hD a b hAB (u j) (hu j) (hClass j)).1
  have hWE : ∀ j, WeakEquation O (Ioo l r) a b (fun _ => 0) (u j) (classicalCaloricGradient (u j)) :=
    fun j => (classicalCaloricGradient_weak_energy O (Ioo l r) hD a b hAB (u j) (hu j) (hClass j)).2
  have hfV : ∀ j, MemLp (u j) 2 (volume.restrict (V ×ˢ Ioo c e)) :=
    fun j => (hf j).mono_measure (Measure.restrict_mono hVD le_rfl)
  have hGV : ∀ j i, MemLp (fun p => classicalCaloricGradient (u j) p i) 2 (volume.restrict (V ×ˢ Ioo c e)) := by
    intro j i
    have h := ((hEnergy j).2 V c e hV hVc hVO hI).2 i
    rwa [productVolume_eq_restrict] at h
  let ev : ℕ → CaloricSpace (V ×ˢ Ioo c e) (hV.prod isOpen_Ioo) a b hABV := fun j =>
    caloricOfWeak V (Ioo c e) (hV.prod isOpen_Ioo) a b hABV (u j) (classicalCaloricGradient (u j))
      (hfV j) (hGV j)
      (weakGradient_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI) (hEnergy j).1)
      (weakEquation_zero_mono (subset_closure.trans hVO) (Ioo_subset_Icc_self.trans hI) (hWE j))
  obtain ⟨Ce,hCe,hBound⟩ := weak_caloric_compact_gradient_integral_bound O l r lam upper hO a b hAB hEll
    Q hQc hQD
  let C : ℝ := max 1 (Real.sqrt Ce)
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hPair : ∀ j k, ‖ev j-ev k‖ ≤ C*‖(hf j).toLp (u j)-(hf k).toLp (u k)‖ := by
    intro j k
    let w : Point d → ℝ := fun p => u j p-u k p
    let G : Point d → RIdx d → ℝ := fun p i => classicalCaloricGradient (u j) p i-classicalCaloricGradient (u k) p i
    have hw : ContDiffOn ℝ ∞ w D := (hu j).sub (hu k)
    have hwClass : ∀ p ∈ D,linearOp D a b w p=0 := by
      intro p hp
      rw [local_linearOp_sub hD a b (hu j) (hu k) hp,hClass j p hp,hClass k p hp,sub_self]
    obtain ⟨hwE,hwWE⟩ := classicalCaloricGradient_weak_energy O (Ioo l r) hD a b hAB w hw hwClass
    obtain ⟨hSum,hIneq⟩ := hBound w (classicalCaloricGradient w) hwE hwWE ((hf j).sub (hf k))
    have hG : ∀ p ∈ Q,∀ i,classicalCaloricGradient w p i=G p i :=
      fun p hp i => classicalCaloricGradient_sub hD (hu j) (hu k) (hQD hp) i
    have hSumEq : (fun p => ∑ i,(classicalCaloricGradient w p i)^2) =ᵐ[volume.restrict Q]
        (fun p => ∑ i,(G p i)^2) := by
      filter_upwards [ae_restrict_mem hQc.measurableSet] with p hp
      exact Finset.sum_congr rfl (fun i _ => congrArg (fun x : ℝ => x^2) (hG p hp i))
    have hSumG := hSum.congr hSumEq
    have hIneqG : (∫ p in Q,∑ i,(G p i)^2) ≤ Ce*(∫ p in D,(w p)^2) := by
      rwa [integral_congr_ae hSumEq] at hIneq
    change ‖(ev j).val-(ev k).val‖ ≤ _
    change ‖((hfV j).toLp (u j),fun i => (hGV j i).toLp (fun p => classicalCaloricGradient (u j) p i))-
      ((hfV k).toLp (u k),fun i => (hGV k i).toLp (fun p => classicalCaloricGradient (u k) p i))‖ ≤ _
    rw [caloric_pair_sub_norm]
    have hNorm := caloric_pair_norm_of_gradient_integral_bound D (V ×ˢ Ioo c e) Q hVD
      (prod_mono subset_closure Ioo_subset_Icc_self) w G ((hf j).sub (hf k)) ((hfV j).sub (hfV k))
      (fun i => (hGV j i).sub (hGV k i)) hSumG Ce hCe.le hIneqG
    have hOuter : (eLpNorm w 2 (volume.restrict D)).toReal=‖(hf j).toLp (u j)-(hf k).toLp (u k)‖ := by
      rw [← MemLp.toLp_sub (hf j) (hf k),Lp.norm_toLp]
      rfl
    simpa only [hOuter,C,w,G] using hNorm
  refine ⟨ev,?_,fun j => (hfV j).coeFn_toLp⟩
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hCauchy (ε/C) (div_pos hε hC)
  refine ⟨N,fun j hj k hk => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ C*‖(hf j).toLp (u j)-(hf k).toLp (u k)‖ := hPair j k
    _ < C*(ε/C) := mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hN j hj k hk) hC
    _ = ε := by field_simp

end Yau.Proofs.F03Aux
