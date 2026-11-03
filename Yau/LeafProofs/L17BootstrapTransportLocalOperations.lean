import Yau.LeafProofs.L17LocalHolderAlgebraBasic

open Set Metric
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapTransportAux
open L17Aux L17HolderAux L17SchauderAux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T gamma : ℝ}

def holderRestrictionElement (u : HolderSpace P T gamma) : LocalHolderSpace ℝ P T gamma :=
  localOfBounds ℝ P T gamma (fun q => holderFun u (chartPoint P T q.1 q.2))
    (continuous_sigma_iff.mpr (fun p => u.val.1.continuous.comp (chartPoint_continuous P T p)))
    ‖u‖ ‖u‖ (fun q => by simpa only [Real.norm_eq_abs] using value_abs_le_norm u _)
    (fun i => by simpa only [Real.norm_eq_abs,smul_eq_mul,localRight,localLeft,chartRight,chartLeft]
      using weighted_difference_abs_le_norm u i)

theorem holderRestrictionElement_norm_le (u : HolderSpace P T gamma) :
    ‖holderRestrictionElement u‖ ≤ ‖u‖ := by
  exact (localOfBounds_norm_le ℝ P T gamma _ _ _ _ (norm_nonneg u) (norm_nonneg u) _ _).trans_eq
    (max_self _)

def holderRestrictionLinearMap : HolderSpace P T gamma →ₗ[ℝ] LocalHolderSpace ℝ P T gamma where
  toFun := holderRestrictionElement
  map_add' u v := by
    apply localFun_injective ℝ P T gamma
    funext q
    rfl
  map_smul' c u := by
    apply localFun_injective ℝ P T gamma
    funext q
    rfl

def holderRestrictionCLM : HolderSpace P T gamma →L[ℝ] LocalHolderSpace ℝ P T gamma :=
  holderRestrictionLinearMap.mkContinuous 1 (fun u => by
    change ‖holderRestrictionElement u‖ ≤ 1*‖u‖
    simpa only [one_mul] using holderRestrictionElement_norm_le u)

theorem holderRestrictionCLM_value (u : HolderSpace P T gamma) (q : LocalCylinder P T) :
    localFun ℝ (holderRestrictionCLM u) q=holderFun u (chartPoint P T q.1 q.2) := rfl

theorem holderRestrictionCLM_norm_le (u : HolderSpace P T gamma) :
    ‖holderRestrictionCLM u‖ ≤ ‖u‖ := holderRestrictionElement_norm_le u

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

def centerMaskedFun (p : P.centers) (u : LocalHolderSpace F P T gamma) (q : LocalCylinder P T) : F :=
  if q.1=p then localFun F u q else 0

theorem centerMaskedFun_continuous (p : P.centers) (u : LocalHolderSpace F P T gamma) :
    Continuous (centerMaskedFun F p u) := by
  apply continuous_sigma_iff.mpr
  intro q
  by_cases hq : q=p
  · subst q
    simp only [centerMaskedFun,ite_true]
    convert! u.val.1.continuous.comp
      (continuous_sigmaMk (i := p) (σ := fun _ : P.centers => ChartCylinder P T)) using 1
  · simp only [centerMaskedFun,hq,ite_false]
    exact continuous_const

theorem centerMaskedFun_norm_le (p : P.centers) (u : LocalHolderSpace F P T gamma)
    (q : LocalCylinder P T) : ‖centerMaskedFun F p u q‖ ≤ ‖u‖ := by
  by_cases hq : q.1=p
  · simpa only [centerMaskedFun,hq,ite_true] using localValue_norm_le F u q
  · simp only [centerMaskedFun,hq,ite_false,norm_zero]
    exact norm_nonneg u

theorem centerMaskedFun_weighted_bound (p : P.centers) (u : LocalHolderSpace F P T gamma)
    (i : ChartPairs P T) :
    ‖pairWeight P T gamma i •
      (centerMaskedFun F p u (localRight P T i)-centerMaskedFun F p u (localLeft P T i))‖ ≤ ‖u‖ := by
  by_cases hi : i.1=p
  · simpa only [centerMaskedFun,localRight,localLeft,hi,ite_true] using localWeighted_difference_norm_le F u i
  · simp only [centerMaskedFun,localRight,localLeft,hi,ite_false,sub_self,smul_zero,norm_zero]
    exact norm_nonneg u

def centerMaskElement (p : P.centers) (u : LocalHolderSpace F P T gamma) : LocalHolderSpace F P T gamma :=
  localOfBounds F P T gamma (centerMaskedFun F p u) (centerMaskedFun_continuous F p u) ‖u‖ ‖u‖
    (centerMaskedFun_norm_le F p u) (centerMaskedFun_weighted_bound F p u)

theorem centerMaskElement_norm_le (p : P.centers) (u : LocalHolderSpace F P T gamma) :
    ‖centerMaskElement F p u‖ ≤ ‖u‖ := by
  exact (localOfBounds_norm_le F P T gamma _ _ _ _ (norm_nonneg u) (norm_nonneg u) _ _).trans_eq
    (max_self _)

def centerMaskLinearMap (p : P.centers) : LocalHolderSpace F P T gamma →ₗ[ℝ] LocalHolderSpace F P T gamma where
  toFun := centerMaskElement F p
  map_add' u v := by
    apply localFun_injective F P T gamma
    funext q
    change centerMaskedFun F p (u+v) q=centerMaskedFun F p u q+centerMaskedFun F p v q
    by_cases hq : q.1=p <;> simp only [centerMaskedFun,hq,ite_true,ite_false]
    · rfl
    · exact (zero_add _).symm
  map_smul' c u := by
    apply localFun_injective F P T gamma
    funext q
    change centerMaskedFun F p (c • u) q=c • centerMaskedFun F p u q
    by_cases hq : q.1=p <;> simp only [centerMaskedFun,hq,ite_true,ite_false,smul_zero]
    rfl

def centerMaskCLM (p : P.centers) : LocalHolderSpace F P T gamma →L[ℝ] LocalHolderSpace F P T gamma :=
  (centerMaskLinearMap F p).mkContinuous 1 (fun u => by
    change ‖centerMaskElement F p u‖ ≤ 1*‖u‖
    simpa only [one_mul] using centerMaskElement_norm_le F p u)

theorem centerMaskCLM_value (p : P.centers) (u : LocalHolderSpace F P T gamma) (q : LocalCylinder P T) :
    localFun F (centerMaskCLM F p u) q=if q.1=p then localFun F u q else 0 := rfl

theorem centerMaskCLM_norm_le (p : P.centers) (u : LocalHolderSpace F P T gamma) :
    ‖centerMaskCLM F p u‖ ≤ ‖u‖ := centerMaskElement_norm_le F p u

end Yau.LeafProofs.L17BootstrapTransportAux
