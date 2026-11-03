import Yau.LeafProofs.L17SchauderSpaceLocal
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Actual bounded bilinear composition in the local Holder graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalHolderAlgebraAux

open L17Aux L17HolderAux L17SchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
variable {P : UniformChartPartition g} {T γ : ℝ}
variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem bilinear_apply_norm_le (B : F →L[ℝ] G →L[ℝ] H) (x : F) (y : G) :
    ‖B x y‖ ≤ ‖B‖*‖x‖*‖y‖ :=
  ((B x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y))

theorem localBilinear_value_bound (B : F →L[ℝ] G →L[ℝ] H)
    (u : LocalHolderSpace F P T γ) (v : LocalHolderSpace G P T γ) (q : LocalCylinder P T) :
    ‖B (localFun F u q) (localFun G v q)‖ ≤ ‖B‖*‖u‖*‖v‖ :=
  (bilinear_apply_norm_le B _ _).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (localValue_norm_le F u q) (norm_nonneg B)) (localValue_norm_le G v q)
    (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg u)))

theorem localBilinear_weighted_bound (B : F →L[ℝ] G →L[ℝ] H)
    (u : LocalHolderSpace F P T γ) (v : LocalHolderSpace G P T γ) (i : ChartPairs P T) :
    ‖pairWeight P T γ i • (B (localFun F u (localRight P T i)) (localFun G v (localRight P T i))-
      B (localFun F u (localLeft P T i)) (localFun G v (localLeft P T i)))‖ ≤ 2*‖B‖*‖u‖*‖v‖ := by
  let x := localLeft P T i
  let y := localRight P T i
  let w := pairWeight P T γ i
  have hForm : w • (B (localFun F u y) (localFun G v y)-B (localFun F u x) (localFun G v x)) =
      B (w • (localFun F u y-localFun F u x)) (localFun G v y)+
        B (localFun F u x) (w • (localFun G v y-localFun G v x)) := by
    simp only [map_smul,map_sub,smul_apply,_root_.sub_apply,smul_sub]
    abel
  rw [hForm]
  calc
    _ ≤ ‖B (w • (localFun F u y-localFun F u x)) (localFun G v y)‖+
        ‖B (localFun F u x) (w • (localFun G v y-localFun G v x))‖ := norm_add_le _ _
    _ ≤ (‖B‖*‖u‖*‖v‖)+(‖B‖*‖u‖*‖v‖) := by
      apply add_le_add
      · exact (bilinear_apply_norm_le B _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (localWeighted_difference_norm_le F u i) (norm_nonneg B))
          (localValue_norm_le G v y) (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg u)))
      · exact (bilinear_apply_norm_le B _ _).trans (mul_le_mul
          (mul_le_mul_of_nonneg_left (localValue_norm_le F u x) (norm_nonneg B))
          (localWeighted_difference_norm_le G v i) (norm_nonneg _) (mul_nonneg (norm_nonneg B) (norm_nonneg u)))
    _ = _ := by ring

def localBilinearElement (B : F →L[ℝ] G →L[ℝ] H)
    (u : LocalHolderSpace F P T γ) (v : LocalHolderSpace G P T γ) : LocalHolderSpace H P T γ :=
  localOfBounds H P T γ (fun q => B (localFun F u q) (localFun G v q))
    ((B.continuous.comp u.val.1.continuous).clm_apply v.val.1.continuous)
    (‖B‖*‖u‖*‖v‖) (2*‖B‖*‖u‖*‖v‖) (localBilinear_value_bound B u v) (localBilinear_weighted_bound B u v)

theorem localBilinearElement_value (B : F →L[ℝ] G →L[ℝ] H)
    (u : LocalHolderSpace F P T γ) (v : LocalHolderSpace G P T γ) (q : LocalCylinder P T) :
    localFun H (localBilinearElement B u v) q=B (localFun F u q) (localFun G v q) := rfl

theorem localBilinearElement_norm_le (B : F →L[ℝ] G →L[ℝ] H)
    (u : LocalHolderSpace F P T γ) (v : LocalHolderSpace G P T γ) :
    ‖localBilinearElement B u v‖ ≤ 2*‖B‖*‖u‖*‖v‖ := by
  apply (localOfBounds_norm_le H P T γ _ _ _ _ (by positivity) (by positivity)
    (localBilinear_value_bound B u v) (localBilinear_weighted_bound B u v)).trans
  exact max_le (by nlinarith [mul_nonneg (mul_nonneg (norm_nonneg B) (norm_nonneg u)) (norm_nonneg v)]) le_rfl

def localBilinearLinearMap (B : F →L[ℝ] G →L[ℝ] H) :
    LocalHolderSpace F P T γ →ₗ[ℝ] LocalHolderSpace G P T γ →ₗ[ℝ] LocalHolderSpace H P T γ where
  toFun u := {
    toFun := localBilinearElement B u
    map_add' := fun v w => by
      apply localFun_injective H P T γ
      funext q
      change B (localFun F u q) (localFun G v q+localFun G w q)=_
      exact (B _).map_add _ _
    map_smul' := fun c v => by
      apply localFun_injective H P T γ
      funext q
      change B (localFun F u q) (c • localFun G v q)=c • B (localFun F u q) (localFun G v q)
      exact (B _).map_smul c _ }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    apply localFun_injective H P T γ
    funext q
    change B (localFun F u q+localFun F v q) (localFun G w q)=_
    rw [B.map_add]
    rfl
  map_smul' c u := by
    apply LinearMap.ext
    intro v
    apply localFun_injective H P T γ
    funext q
    change B (c • localFun F u q) (localFun G v q)=_
    rw [B.map_smul]
    rfl

def localBilinearCLM (B : F →L[ℝ] G →L[ℝ] H) :
    LocalHolderSpace F P T γ →L[ℝ] LocalHolderSpace G P T γ →L[ℝ] LocalHolderSpace H P T γ :=
  (localBilinearLinearMap B).mkContinuous₂ (2*‖B‖) (localBilinearElement_norm_le B)

theorem localBilinearCLM_value (B : F →L[ℝ] G →L[ℝ] H)
    (u : LocalHolderSpace F P T γ) (v : LocalHolderSpace G P T γ) (q : LocalCylinder P T) :
    localFun H (localBilinearCLM B u v) q=B (localFun F u q) (localFun G v q) := rfl

theorem localBilinearCLM_opNorm_le (B : F →L[ℝ] G →L[ℝ] H) :
    ‖localBilinearCLM (P := P) (T := T) (γ := γ) B‖ ≤ 2*‖B‖ :=
  (localBilinearLinearMap B).mkContinuous₂_norm_le (by positivity) (localBilinearElement_norm_le B)

end Yau.LeafProofs.L17LocalHolderAlgebraAux
