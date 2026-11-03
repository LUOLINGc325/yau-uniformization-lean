import Yau.LeafProofs.L17GaussianResidualOperator
import Yau.LeafProofs.L17GaussianSmallTime

/-! The actual scalar parabolic operator has a genuine bounded inverse
at both Holder exponents on one atlas and one closed time interval. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open L17HolderAux L17SchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance linear_iso_add_group {P : UniformChartPartition g} {T γ : ℝ} {hT : 0 < T} :
    AddCommGroup (SchauderSpace P T γ hT) :=
  (schauderSpace_normedAddCommGroup P T γ hT).toAddCommGroup
local instance linear_iso_normed_space {P : UniformChartPartition g} {T γ : ℝ} {hT : 0 < T} :
    NormedSpace ℝ (SchauderSpace P T γ hT) := schauderSpace_normedSpace P T γ hT

abbrev flowHighExponent : Ioo (0 : ℝ) 1 := ⟨1/2,by constructor <;> norm_num⟩
abbrev flowLowExponent : Ioo (0 : ℝ) 1 := ⟨1/4,by constructor <;> norm_num⟩

theorem BoundedChartFamily.exists_two_exponent_scalar_isomorphisms
    (A : BoundedChartFamily g) (hg : MetricSmooth g) :
    ∃ Cα Cβ : ℝ, 0 < Cα ∧ 0 < Cβ ∧ ∀ ε : ℝ, 0 < ε → ∃ P : UniformChartPartition g,
      P.charts=A ∧ P.radius<ε ∧ ∃ hr : P.radius≤1, 2*P.radius<A.radius ∧ ∃ T : ℝ,
        ∃ hT : 0 < T, ∃ hSmall : T ≤ P.radius^2,
          ∃ Sα : SchauderSpace P T (1/2 : ℝ) hT ≃L[ℝ] HolderSpace P T (1/2 : ℝ),
          ∃ Sβ : SchauderSpace P T (1/4 : ℝ) hT ≃L[ℝ] HolderSpace P T (1/4 : ℝ),
            (Sα : SchauderSpace P T (1/2 : ℝ) hT →L[ℝ] HolderSpace P T (1/2 : ℝ)) =
              scalarParabolicCLM P T (1/2 : ℝ) hT hSmall (by norm_num) hr ∧
            (Sβ : SchauderSpace P T (1/4 : ℝ) hT →L[ℝ] HolderSpace P T (1/4 : ℝ)) =
              scalarParabolicCLM P T (1/4 : ℝ) hT hSmall (by norm_num) hr ∧
            ‖(Sα.symm : HolderSpace P T (1/2 : ℝ) →L[ℝ] SchauderSpace P T (1/2 : ℝ) hT)‖ ≤ Cα ∧
            ‖(Sβ.symm : HolderSpace P T (1/4 : ℝ) →L[ℝ] SchauderSpace P T (1/4 : ℝ) hT)‖ ≤ Cβ := by
  obtain ⟨D,E,hD,hE,hPart⟩ := A.exists_uniform_approximate_scalar_inverse hg
  obtain ⟨ε0,S,hε0,hS,hSone,hScales⟩ := exists_common_gaussian_small_scales (E flowHighExponent) (E flowLowExponent)
  refine ⟨(4/3)*D flowHighExponent,(4/3)*D flowLowExponent,
    mul_pos (by norm_num) (hD _),mul_pos (by norm_num) (hD _),?_⟩
  intro ε hε
  obtain ⟨P,hA,hρδ,hr,hρA,hAll⟩ := hPart (min ε ε0) (lt_min hε hε0)
  have hρε : P.radius<ε := hρδ.trans_le (min_le_left _ _)
  have hρε0 : P.radius<ε0 := hρδ.trans_le (min_le_right _ _)
  let T := P.radius^2*S
  have hT : 0 < T := mul_pos (sq_pos_of_pos P.radius_pos) hS
  have hSmall : T ≤ P.radius^2 := by
    change P.radius^2*S ≤ P.radius^2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hSone (sq_nonneg P.radius)
  have hRatio : T/P.radius^2=S := by dsimp only [T]; field_simp [P.radius_pos.ne']
  obtain ⟨Qα,hValα,hQα,hErrα⟩ := hAll T hT hSmall hr flowHighExponent
  obtain ⟨Qβ,hValβ,hQβ,hErrβ⟩ := hAll T hT hSmall hr flowLowExponent
  have hExpα : (1-flowHighExponent.val)/2=(1/4 : ℝ) := by norm_num [flowHighExponent]
  have hExpβ : (1-flowLowExponent.val)/2=(3/8 : ℝ) := by norm_num [flowLowExponent]
  rw [hRatio,hExpα] at hErrα
  rw [hRatio,hExpβ] at hErrβ
  obtain ⟨hσα,hσβ⟩ := hScales P.radius P.radius_pos hρε0
  let Pα := scalarParabolicCLM P T (1/2 : ℝ) hT hSmall (by norm_num) hr
  let Pβ := scalarParabolicCLM P T (1/4 : ℝ) hT hSmall (by norm_num) hr
  have hSmallα : ‖Pα.comp Qα-ContinuousLinearMap.id ℝ (HolderSpace P T (1/2 : ℝ))‖ ≤ 1/4 :=
    hErrα.trans hσα.le
  have hSmallβ : ‖Pβ.comp Qβ-ContinuousLinearMap.id ℝ (HolderSpace P T (1/4 : ℝ))‖ ≤ 1/4 :=
    hErrβ.trans hσβ.le
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
  refine ⟨P,hA,hρε,hr,hρA,T,hT,hSmall,Sα,Sβ,rfl,rfl,?_,?_⟩
  · rw [hSymmα]
    exact (correctedParametrix_norm_le Pα Qα hSmallα).trans
      (mul_le_mul_of_nonneg_left hQα (by norm_num))
  · rw [hSymmβ]
    exact (correctedParametrix_norm_le Pβ Qβ hSmallβ).trans
      (mul_le_mul_of_nonneg_left hQβ (by norm_num))

end Yau.LeafProofs.L17Aux
