import Yau.LeafProofs.L17SchauderSpaceLocal

/-! Actual pointwise continuous linear maps on the local Holder graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalHolderAlgebraAux

open L17Aux L17HolderAux L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T γ : ℝ}
variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem localMap_value_bound (L : F →L[ℝ] G) (u : LocalHolderSpace F P T γ) (q : LocalCylinder P T) :
    ‖L (localFun F u q)‖ ≤ ‖L‖*‖u‖ :=
  (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (localValue_norm_le F u q) (norm_nonneg L))

theorem localMap_weighted_bound (L : F →L[ℝ] G) (u : LocalHolderSpace F P T γ) (i : ChartPairs P T) :
    ‖pairWeight P T γ i • (L (localFun F u (localRight P T i))-L (localFun F u (localLeft P T i)))‖ ≤ ‖L‖*‖u‖ := by
  rw [← map_sub,← map_smul]
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (localWeighted_difference_norm_le F u i) (norm_nonneg L))

def localMapElement (L : F →L[ℝ] G) (u : LocalHolderSpace F P T γ) : LocalHolderSpace G P T γ :=
  localOfBounds G P T γ (fun q => L (localFun F u q)) (L.continuous.comp u.val.1.continuous)
    (‖L‖*‖u‖) (‖L‖*‖u‖) (localMap_value_bound L u) (localMap_weighted_bound L u)

theorem localMapElement_value (L : F →L[ℝ] G) (u : LocalHolderSpace F P T γ) (q : LocalCylinder P T) :
    localFun G (localMapElement L u) q=L (localFun F u q) := rfl

theorem localMapElement_norm_le (L : F →L[ℝ] G) (u : LocalHolderSpace F P T γ) :
    ‖localMapElement L u‖ ≤ ‖L‖*‖u‖ := by
  simpa only [localMapElement,max_self] using localOfBounds_norm_le G P T γ _ _ _ _ (by positivity) (by positivity)
    (localMap_value_bound L u) (localMap_weighted_bound L u)

def localMapLinearMap (L : F →L[ℝ] G) : LocalHolderSpace F P T γ →ₗ[ℝ] LocalHolderSpace G P T γ where
  toFun := localMapElement L
  map_add' u v := by
    apply localFun_injective G P T γ
    funext q
    change L (localFun F u q+localFun F v q)=L (localFun F u q)+L (localFun F v q)
    exact L.map_add _ _
  map_smul' c u := by
    apply localFun_injective G P T γ
    funext q
    change L (c • localFun F u q)=c • L (localFun F u q)
    exact L.map_smul c _

def localMapCLM (L : F →L[ℝ] G) : LocalHolderSpace F P T γ →L[ℝ] LocalHolderSpace G P T γ :=
  (localMapLinearMap L).mkContinuous ‖L‖ (localMapElement_norm_le L)

theorem localMapCLM_value (L : F →L[ℝ] G) (u : LocalHolderSpace F P T γ) (q : LocalCylinder P T) :
    localFun G (localMapCLM L u) q=L (localFun F u q) := rfl

theorem localMapCLM_opNorm_le (L : F →L[ℝ] G) :
    ‖localMapCLM (P := P) (T := T) (γ := γ) L‖ ≤ ‖L‖ :=
  (localMapCLM L).opNorm_le_bound (norm_nonneg L) (localMapElement_norm_le L)

end Yau.LeafProofs.L17LocalHolderAlgebraAux
