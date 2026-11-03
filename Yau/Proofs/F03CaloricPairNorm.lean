import Yau.Proofs.F03CaloricNorms

/-! A genuine compact energy estimate controls the actual value/gradient L² pair. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
namespace Yau.Proofs.F03Aux
open Yau Parabolic
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem caloric_pair_norm_of_gradient_integral_bound
    (U V K : Set (Point d)) (hVU : V ⊆ U) (hVK : V ⊆ K)
    (u : Point d → ℝ) (G : Point d → RIdx d → ℝ)
    (huU : MemLp u 2 (volume.restrict U)) (huV : MemLp u 2 (volume.restrict V))
    (hGV : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict V))
    (hSum : Integrable (fun p => ∑ i,(G p i)^2) (volume.restrict K))
    (C : ℝ) (hC : 0 ≤ C)
    (hEnergy : (∫ p in K,∑ i,(G p i)^2) ≤ C*(∫ p in U,(u p)^2)) :
    ‖((huV.toLp u,fun i => (hGV i).toLp (fun p => G p i)) : CaloricAmbient V)‖ ≤
      max 1 (Real.sqrt C)*(eLpNorm u 2 (volume.restrict U)).toReal := by
  let N : ℝ := (eLpNorm u 2 (volume.restrict U)).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hValue : ‖huV.toLp u‖ ≤ N := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono huU.eLpNorm_ne_top
      (eLpNorm_mono_measure u (Measure.restrict_mono hVU le_rfl))
  have hNormU : (∫ p in U,(u p)^2)=N^2 := by
    rw [← real_norm_toLp_sq_eq_integral (volume.restrict U) u huU,Lp.norm_toLp]
  have hSumV := hSum.mono_measure (Measure.restrict_mono hVK le_rfl)
  have hGradient : ∀ i, ‖(hGV i).toLp (fun p => G p i)‖ ≤ Real.sqrt C*N := by
    intro i
    apply real_norm_toLp_le_sqrt_mul (volume.restrict V) (fun p => G p i) (hGV i) C N hC hN
    have hSq : Integrable (fun p => (G p i)^2) (volume.restrict V) := by
      apply ((hGV i).integrable_mul (hGV i)).congr
      exact ae_of_all _ (fun p => by change G p i*G p i=(G p i)^2;ring)
    calc
      _ ≤ ∫ p in V,∑ j,(G p j)^2 := by
        apply integral_mono hSq hSumV
        intro p
        exact Finset.single_le_sum (fun j _ => sq_nonneg (G p j)) (Finset.mem_univ i)
      _ ≤ ∫ p in K,∑ j,(G p j)^2 := by
        apply setIntegral_mono_set hSum
        · exact ae_of_all _ (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg (G p j)))
        · exact Filter.Eventually.of_forall hVK
      _ ≤ C*N^2 := by simpa only [hNormU] using hEnergy
  apply caloricAmbient_norm_le V _ _ (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hN)
  · calc
      _ ≤ N := hValue
      _ = 1*N := (one_mul N).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left 1 (Real.sqrt C)) hN
  · intro i
    exact (hGradient i).trans (mul_le_mul_of_nonneg_right (le_max_right 1 (Real.sqrt C)) hN)

end Yau.Proofs.F03Aux
