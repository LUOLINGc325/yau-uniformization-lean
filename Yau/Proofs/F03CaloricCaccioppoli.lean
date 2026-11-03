import Yau.Proofs.F03CaloricCaccioppoliCutoff

/-! A fixed compact gradient estimate for actual weak caloric fields. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

theorem weak_caloric_compact_gradient_integral_bound
    (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (K : Set (Point d)) (hK : IsCompact K) (hKD : K ⊆ O ×ˢ Ioo l r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Point d → ℝ) (G : Point d → RIdx d → ℝ),
      LocalEnergy O (Ioo l r) u G → WeakEquation O (Ioo l r) a b (fun _ => 0) u G →
      MemLp u 2 (volume.restrict (O ×ˢ Ioo l r)) →
      Integrable (fun p => ∑ i,(G p i)^2) (volume.restrict K) ∧
      (∫ p in K,∑ i,(G p i)^2) ≤ C*(∫ p in O ×ˢ Ioo l r,(u p)^2) := by
  obtain ⟨η,hη,hηrange,hηnear⟩ := exists_nonnegative_test_eq_one_near_compact (hO.prod isOpen_Ioo) hK hKD
  obtain ⟨C,hC,hBound⟩ := weak_caloric_test_gradient_integral_bound O l r lam upper hO a b hAB hEll η hη hηrange
  refine ⟨C,hC,?_⟩
  intro u G hE hWE hu
  obtain ⟨hWeighted,hIneq⟩ := hBound u G hE hWE hu
  have hKG := localEnergy_memLp_on_compact hO hE hK hKD
  have hEach : ∀ i, Integrable (fun p => (G p i)^2) (volume.restrict K) := by
    intro i
    apply ((hKG.2 i).integrable_mul (hKG.2 i)).congr
    exact ae_of_all _ (fun p => by change G p i*G p i=(G p i)^2;ring)
  have hi : Integrable (fun p => ∑ i,(G p i)^2) (volume.restrict K) :=
    integrable_finsetSum Finset.univ (fun i _ => hEach i)
  refine ⟨hi,?_⟩
  calc
    _ = ∫ p in K,η p^2*(∑ i,(G p i)^2) := by
      apply setIntegral_congr_fun hK.measurableSet
      intro p hp
      have hηone : η p=1 := (hηnear p hp).eq_of_nhds
      change (∑ i,(G p i)^2)=η p^2*(∑ i,(G p i)^2)
      rw [hηone]
      norm_num
    _ ≤ ∫ p,η p^2*(∑ i,(G p i)^2) := by
      apply setIntegral_le_integral hWeighted
      exact ae_of_all _ (fun p => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    _ ≤ _ := hIneq

end Yau.Proofs.F03Aux
