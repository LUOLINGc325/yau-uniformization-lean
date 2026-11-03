import Yau.Proofs.F03HeatCorrectionUniformAnnulus
import Yau.Proofs.F03DyadicLeviError
import Yau.Proofs.F03HermitianFiniteBudget

/-! The actual dyadic correction recovers the metric defect with a genuinely decaying Levi error. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder Matrix
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings LeafProofs.L18Aux
variable {n : ℕ}

theorem metricDefectDyadicCorrection_levi_lower_bound (hP06 : P06) (hP07 : P07) (hP08 : P08)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ,0 < C ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
        (s : ℝ),s ∈ Icc 0 T → ∀ x,
      HermLE (gMat X.metric.form x-gMat (h s) x-
        Complex.ofReal (C/(u x)^(heatDecayExponent n)) • gMat X.metric.form x)
        (levi (fun y => metricDefectDyadicCorrection X h μ hμ O hO u y s) x) := by
  obtain ⟨B,hB,hAnnulus⟩ := metricDefectHeatCorrection_uniform_annulus hP06 hP07 hP08 X o h U P ρ hf u hu hT
  obtain ⟨Q,hQ,hProfile⟩ := controlledExhaustion_dyadic_profile_bounds X o u hu
  refine ⟨B+9*B*Q,by positivity,fun μ hμ O hO s hs x => ?_⟩
  let F : ℕ → Pt X → ℝ → ℝ := fun j => metricDefectHeatCorrection X h μ hμ O hO ((2:ℝ)^j)
  let G := gMat X.metric.form x
  let D := G-gMat (h s) x
  let c : ℕ → ℝ := fun j => dyadicPartition j (u x)
  let E : ℕ → Herm n := fun j => dyadicLeviError u (fun y => F j y s) j x
  let M := 3*B*Q/(u x)^(heatDecayExponent n)
  have hu1 := hu.2.2.1 x
  have hu0 : 0 < u x := zero_lt_one.trans_le hu1
  have hG : G.PosSemidef := (hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  have hM : 0 ≤ M := by dsimp [M];positivity
  have hSmooth (j : ℕ) : SmoothFn (fun y => F j y s) :=
    metricDefectHeatCorrection_smooth X o h U P ρ hf μ hμ O hO _ hs.1
  obtain ⟨N,hPartition,hIdentity⟩ := dyadicGluing_levi_finite_identity u hu.1 F s hSmooth x hu1
  have hMain : HermLE (D-Complex.ofReal (B/(u x)^(heatDecayExponent n)) • G)
      (∑ j ∈ Finset.range (N+1),Complex.ofReal (c j) • levi (fun y => F j y s) x) := by
    have hRow (j : ℕ) : HermLE
        (Complex.ofReal (c j) • (D-Complex.ofReal (B/(u x)^(heatDecayExponent n)) • G))
        (Complex.ofReal (c j) • levi (fun y => F j y s) x) := by
      by_cases hZero : c j=0
      · simp only [hZero,Complex.ofReal_zero,zero_smul]
        exact hermLE_refl 0
      have hBand := dyadicPartition_scale_support hu1 j hZero
      exact hermLE_real_smul (hAnnulus μ hμ O hO s hs j x hBand.1 hBand.2).2.2
        (dyadicPartition_nonnegative j (zero_le_one.trans hu1))
    have hTotal := hermLE_sum (Finset.range (N+1)) _ _ (fun j _ => hRow j)
    have hLeft : (∑ j ∈ Finset.range (N+1),Complex.ofReal (c j) •
        (D-Complex.ofReal (B/(u x)^(heatDecayExponent n)) • G))=
        D-Complex.ofReal (B/(u x)^(heatDecayExponent n)) • G := by
      rw [← Finset.sum_smul,← Complex.ofReal_sum]
      change Complex.ofReal (∑ j ∈ Finset.range (N+1),dyadicPartition j (u x)) • _=_
      rw [hPartition,Complex.ofReal_one,one_smul]
    rwa [hLeft] at hTotal
  obtain ⟨q,hTail⟩ := dyadicPartition_common_active_band hu1
  have hError (j : ℕ) : HermAbsLE (E j) G M := by
    by_cases hBand : (2:ℝ)^j/2 ≤ u x ∧ u x ≤ 2*(2:ℝ)^j
    · have hData := hAnnulus μ hμ O hO s hs j x hBand.1 hBand.2
      exact dyadicLeviError_abs_bound X.metric.form u (fun y => F j y s) hu.1 (hSmooth j) j x
        hB hQ hu0 (hProfile j x).1 (hProfile j x).2 hData.1 hData.2.1
    · have hZero : deriv (dyadicPartition j) (u x)=0 := by
        by_contra hh
        exact hBand (dyadicPartition_deriv_scale_support hu1 j hh)
      have hZero' : deriv (deriv (dyadicPartition j)) (u x)=0 := by
        by_contra hh
        exact hBand (dyadicPartition_secondDeriv_scale_support hu1 j hh)
      change HermAbsLE (dyadicLeviError u (fun y => F j y s) j x) G M
      rw [dyadicLeviError_zero u _ hu.1 j x hZero hZero']
      exact hermAbsLE_mono hG (hermAbsLE_zero G) hM
  have hErrorTail (j : ℕ) (hj : j+1 < q ∨ q+1 < j) : E j=0 :=
    dyadicLeviError_zero u _ hu.1 j x (hTail j hj).2.1 (hTail j hj).2.2
  have hErrorTotal := hermAbsLE_adjacent_sum q (Finset.range (N+1)) E G hG hM
    (fun j _ => hError j) (fun j _ hj => hErrorTail j hj)
  have hFull := hermLE_add hMain hErrorTotal.1
  have hGrouped : levi (fun y => dyadicGluing u F y s) x=
      (∑ j ∈ Finset.range (N+1),Complex.ofReal (c j) • levi (fun y => F j y s) x)+
      ∑ j ∈ Finset.range (N+1),E j := by
    rw [hIdentity]
    dsimp only [c,E,dyadicLeviError]
    simp only [Finset.sum_add_distrib]
    abel
  change HermLE (D-Complex.ofReal ((B+9*B*Q)/(u x)^(heatDecayExponent n)) • G)
    (levi (fun y => dyadicGluing u F y s) x)
  rw [hGrouped]
  convert hFull using 1
  ext a b
  simp only [M,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_neg]
  norm_num
  ring

end Yau.Proofs.F03Aux
