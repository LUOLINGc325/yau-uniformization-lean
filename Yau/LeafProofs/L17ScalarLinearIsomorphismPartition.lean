import Yau.LeafProofs.L17ScalarLinearIsomorphism
import Yau.LeafProofs.L17GaussianInversePartition
import Yau.LeafProofs.L17GaussianSmallTime

/-! The actual scalar parabolic operator has a genuine bounded inverse
at both Holder exponents, retaining the actual atlas budgets and all smaller times. -/

open Set Metric
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open L17HolderAux L17SchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance linear_iso_partition_add_group {P : UniformChartPartition g} {T γ : ℝ} {hT : 0 < T} :
    AddCommGroup (SchauderSpace P T γ hT) :=
  (schauderSpace_normedAddCommGroup P T γ hT).toAddCommGroup
local instance linear_iso_partition_normed_space {P : UniformChartPartition g} {T γ : ℝ} {hT : 0 < T} :
    NormedSpace ℝ (SchauderSpace P T γ hT) := schauderSpace_normedSpace P T γ hT



theorem BoundedChartFamily.exists_two_exponent_scalar_isomorphisms_with_partition
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ N : ℕ, ∃ B : ℕ → ℝ, ∃ Cα Cβ S : ℝ,
      (∀ k,0<B k) ∧ 0<Cα ∧ 0<Cβ ∧ 0<S ∧ S≤1 ∧
      ∀ ε : ℝ, 0<ε → ∃ P : UniformChartPartition g,
        P.charts=A ∧ P.radius<ε ∧ P.overlapBudget=N ∧
        (∀ k (p : P.centers) q z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
          ‖iteratedFDeriv ℝ k (fun w => P.weight p (P.charts.chart q w)) z‖ ≤ B k*(P.radius⁻¹)^k ∧
          ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart q w)) z‖ ≤ B k*(P.radius⁻¹)^k) ∧
        ∃ hr : P.radius≤1, 2*P.radius<A.radius ∧
        ∀ (T : ℝ) (hT : 0<T), T≤P.radius^2*S → ∃ hSmall : T≤P.radius^2,
          ∃ Sα : SchauderSpace P T (1/2 : ℝ) hT ≃L[ℝ] HolderSpace P T (1/2 : ℝ),
          ∃ Sβ : SchauderSpace P T (1/4 : ℝ) hT ≃L[ℝ] HolderSpace P T (1/4 : ℝ),
            (Sα : SchauderSpace P T (1/2 : ℝ) hT →L[ℝ] HolderSpace P T (1/2 : ℝ)) =
              scalarParabolicCLM P T (1/2 : ℝ) hT hSmall (by norm_num) hr ∧
            (Sβ : SchauderSpace P T (1/4 : ℝ) hT →L[ℝ] HolderSpace P T (1/4 : ℝ)) =
              scalarParabolicCLM P T (1/4 : ℝ) hT hSmall (by norm_num) hr ∧
            ‖(Sα.symm : HolderSpace P T (1/2 : ℝ) →L[ℝ] SchauderSpace P T (1/2 : ℝ) hT)‖ ≤ Cα ∧
            ‖(Sβ.symm : HolderSpace P T (1/4 : ℝ) →L[ℝ] SchauderSpace P T (1/4 : ℝ) hT)‖ ≤ Cβ := by
  obtain ⟨N,B,D,E,hB,hD,hE,hPart⟩ := A.exists_uniform_approximate_scalar_inverse_with_partition hg
  obtain ⟨ε0,S,hε0,hS,hSone,hScales⟩ := exists_common_gaussian_small_scales (E flowHighExponent) (E flowLowExponent)
  refine ⟨N,B,(4/3)*D flowHighExponent,(4/3)*D flowLowExponent,S,hB,
    mul_pos (by norm_num) (hD _),mul_pos (by norm_num) (hD _),hS,hSone,?_⟩
  intro ε hε
  obtain ⟨P,hA,hρδ,hr,hρA,hN,hJets,hAll⟩ := hPart (min ε ε0) (lt_min hε hε0)
  have hρε : P.radius<ε := hρδ.trans_le (min_le_left _ _)
  have hρε0 : P.radius<ε0 := hρδ.trans_le (min_le_right _ _)
  refine ⟨P,hA,hρε,hN,hJets,hr,hρA,?_⟩
  intro T hT hTime
  have hSmall : T≤P.radius^2 := hTime.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hSone (sq_nonneg P.radius))
  have hRatio : T/P.radius^2≤S := (div_le_iff₀ (sq_pos_of_pos P.radius_pos)).mpr (by simpa only [mul_comm] using hTime)
  have hRatioPos : 0<T/P.radius^2 := div_pos hT (sq_pos_of_pos P.radius_pos)
  obtain ⟨Qα,hValα,hQα,hErrα⟩ := hAll T hT hSmall hr flowHighExponent
  obtain ⟨Qβ,hValβ,hQβ,hErrβ⟩ := hAll T hT hSmall hr flowLowExponent
  have hExpα : (1-flowHighExponent.val)/2=(1/4 : ℝ) := by norm_num [flowHighExponent]
  have hExpβ : (1-flowLowExponent.val)/2=(3/8 : ℝ) := by norm_num [flowLowExponent]
  rw [hExpα] at hErrα
  rw [hExpβ] at hErrβ
  have hPowα : (T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^(1/4 : ℝ)≤S^(1/2 : ℝ)+S^(1/4 : ℝ) :=
    add_le_add (Real.rpow_le_rpow hRatioPos.le hRatio (by norm_num))
      (Real.rpow_le_rpow hRatioPos.le hRatio (by norm_num))
  have hPowβ : (T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^(3/8 : ℝ)≤S^(1/2 : ℝ)+S^(3/8 : ℝ) :=
    add_le_add (Real.rpow_le_rpow hRatioPos.le hRatio (by norm_num))
      (Real.rpow_le_rpow hRatioPos.le hRatio (by norm_num))
  have hErrα' := hErrα.trans (mul_le_mul_of_nonneg_left
    (show P.radius+(T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^(1/4 : ℝ)≤
      P.radius+S^(1/2 : ℝ)+S^(1/4 : ℝ) by linarith [hPowα]) (hE flowHighExponent).le)
  have hErrβ' := hErrβ.trans (mul_le_mul_of_nonneg_left
    (show P.radius+(T/P.radius^2)^(1/2 : ℝ)+(T/P.radius^2)^(3/8 : ℝ)≤
      P.radius+S^(1/2 : ℝ)+S^(3/8 : ℝ) by linarith [hPowβ]) (hE flowLowExponent).le)
  obtain ⟨hσα,hσβ⟩ := hScales P.radius P.radius_pos hρε0
  let Pα := scalarParabolicCLM P T (1/2 : ℝ) hT hSmall (by norm_num) hr
  let Pβ := scalarParabolicCLM P T (1/4 : ℝ) hT hSmall (by norm_num) hr
  have hSmallα : ‖Pα.comp Qα-ContinuousLinearMap.id ℝ (HolderSpace P T (1/2 : ℝ))‖ ≤ 1/4 :=
    hErrα'.trans hσα.le
  have hSmallβ : ‖Pβ.comp Qβ-ContinuousLinearMap.id ℝ (HolderSpace P T (1/4 : ℝ))‖ ≤ 1/4 :=
    hErrβ'.trans hσβ.le
  have hltα : ‖Pα.comp Qα-ContinuousLinearMap.id ℝ (HolderSpace P T (1/2 : ℝ))‖ < 1 := by linarith
  have hltβ : ‖Pβ.comp Qβ-ContinuousLinearMap.id ℝ (HolderSpace P T (1/4 : ℝ))‖ < 1 := by linarith
  have hIα : Function.Injective Pα := L17ParabolicUniquenessAux.scalarParabolicCLM_injective
    (P := P) (T := T) (gamma := (1/2 : ℝ)) (hT := hT) hSmall (by norm_num) hr
  have hIβ : Function.Injective Pβ := L17ParabolicUniquenessAux.scalarParabolicCLM_injective
    (P := P) (T := T) (gamma := (1/4 : ℝ)) (hT := hT) hSmall (by norm_num) hr
  let Sα := correctedParametrixEquiv Pα Qα hltα hIα
  let Sβ := correctedParametrixEquiv Pβ Qβ hltβ hIβ
  have hSymmα : (Sα.symm : HolderSpace P T (1/2 : ℝ) →L[ℝ] SchauderSpace P T (1/2 : ℝ) hT) =
      correctedParametrix Pα Qα := by
    apply ContinuousLinearMap.ext
    intro f
    exact correctedParametrixEquiv_symm_apply Pα Qα hltα hIα f
  have hSymmβ : (Sβ.symm : HolderSpace P T (1/4 : ℝ) →L[ℝ] SchauderSpace P T (1/4 : ℝ) hT) =
      correctedParametrix Pβ Qβ := by
    apply ContinuousLinearMap.ext
    intro f
    exact correctedParametrixEquiv_symm_apply Pβ Qβ hltβ hIβ f
  refine ⟨hSmall,Sα,Sβ,rfl,rfl,?_,?_⟩
  · rw [hSymmα]
    exact (correctedParametrix_norm_le Pα Qα hSmallα).trans
      (mul_le_mul_of_nonneg_left hQα (by norm_num))
  · rw [hSymmβ]
    exact (correctedParametrix_norm_le Pβ Qβ hSmallβ).trans
      (mul_le_mul_of_nonneg_left hQβ (by norm_num))

end Yau.LeafProofs.L17Aux
