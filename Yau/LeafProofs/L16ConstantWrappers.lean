import Yau.LeafProofs.L16

/-! Small-time jets and first-jet Hölder transport for the constant heat solver. -/

noncomputable section

namespace Yau.LeafProofs.L16Aux

open Yau.Parabolic Yau.ParabolicCandidates

/-- The explicit coordinate-change factor for the constant heat solver. -/
def constantHeatNormFactor {n : ℕ} (α : ℝ) (B : Space n ≃L[ℝ] Space n) : ℝ :=
  (1+‖(B : Space n →L[ℝ] Space n)‖^α)*
    (1+‖(B.symm : Space n →L[ℝ] Space n)‖)^2*
    (1+‖(B.symm : Space n →L[ℝ] Space n)‖^α)

/-- Pull back the value and genuine spatial derivative together. -/
def firstJetPullback {n : ℕ} (L : Space n ≃L[ℝ] Space n) :
    (ℝ × (Space n →L[ℝ] ℝ)) →L[ℝ] (ℝ × (Space n →L[ℝ] ℝ)) :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap
    (gradientPullback L : (Space n →L[ℝ] ℝ) →L[ℝ] (Space n →L[ℝ] ℝ))

@[simp] theorem firstJetPullback_apply {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (v : ℝ) (G : Space n →L[ℝ] ℝ) :
    firstJetPullback L (v,G) = (v,gradientPullback L G) := rfl

theorem firstJetPullback_norm_le {n : ℕ} (L : Space n ≃L[ℝ] Space n) :
    ‖firstJetPullback L‖ ≤ (1+‖(L : Space n →L[ℝ] Space n)‖)^2 := by
  let K : ℝ := ‖(L : Space n →L[ℝ] Space n)‖
  have hK : 0 ≤ K := norm_nonneg _
  have hOne : 1 ≤ (1+K)^2 := by nlinarith [sq_nonneg K]
  have hKN : K ≤ (1+K)^2 := by nlinarith [sq_nonneg K]
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro z
  change max ‖z.1‖ ‖gradientPullback L z.2‖ ≤ (1+K)^2*‖z‖
  apply max_le
  · exact (le_max_left ‖z.1‖ ‖z.2‖).trans
      (by simpa only [one_mul,Prod.norm_def] using mul_le_mul_of_nonneg_right hOne (norm_nonneg z))
  · calc
      _ ≤ K*‖z.2‖ := gradientPullback_norm_le L z.2
      _ ≤ (1+K)^2*‖z‖ := mul_le_mul hKN (le_max_right ‖z.1‖ ‖z.2‖)
        (norm_nonneg _) (sq_nonneg _)

/-- Uniform small pointwise value, gradient, and Hessian bounds, including time zero. -/
theorem constantHeatDuhamel_small_jet_bounds {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Space n ≃L[ℝ] Space n) (T F : ℝ),
      0 ≤ T → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      ∀ p ∈ cylinder Set.univ 0 T,
        |constantHeatDuhamel B f p| ≤ C*F*constantHeatNormFactor α B*p.2 ∧
        ‖spatialD (constantHeatDuhamel B f) p‖ ≤
          C*F*constantHeatNormFactor α B*p.2^(1/2:ℝ) ∧
        ‖spatialDD (constantHeatDuhamel B f) p‖ ≤
          C*F*constantHeatNormFactor α B*p.2^(α/2) := by
  obtain ⟨C,hC,hDer⟩ := heatDuhamel_derivative_bounds_of_holder (n := n) hα
  refine ⟨C+1,by positivity,?_⟩
  intro B T F hT f hf p hp
  let W : ℝ := 1+‖(B : Space n →L[ℝ] Space n)‖^α
  let K : ℝ := ‖(B.symm : Space n →L[ℝ] Space n)‖
  let R : ℝ := (1+K)^2
  let V : ℝ := 1+K^α
  have hK : 0 ≤ K := norm_nonneg _
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hV1 : 1 ≤ V := le_add_of_nonneg_right (Real.rpow_nonneg hK _)
  have hR1 : 1 ≤ R := by dsimp [R]; nlinarith [sq_nonneg K]
  have hKR : K ≤ R := by dsimp [R]; nlinarith [sq_nonneg K]
  have hK2R : K^2 ≤ R := by dsimp [R]; nlinarith
  have hR : 0 ≤ R := zero_le_one.trans hR1
  have hRV : R ≤ R*V := by simpa using mul_le_mul_of_nonneg_left hV1 hR
  have hg : HolderBound α (cylinder Set.univ 0 T) (spaceTimePullback B f) (F*W) :=
    holderBound_comp_spaceLinearMap hα.le (B : Space n →L[ℝ] Space n) hf
  have hFW : 0 ≤ F*W := hg.1
  have hBudget : F*W ≤ (C+1)*F*constantHeatNormFactor α B := by
    have hOne : (1:ℝ) ≤ (C+1)*(R*V) := by
      calc
        _ = 1*1 := by ring
        _ ≤ (C+1)*(R*V) := mul_le_mul (by linarith) (hR1.trans hRV)
          zero_le_one (by positivity)
    calc
      _ = (F*W)*1 := by ring
      _ ≤ (F*W)*((C+1)*(R*V)) := mul_le_mul_of_nonneg_left hOne hFW
      _ = _ := by dsimp [constantHeatNormFactor,W,R,V,K]; ring
  have hGradBudget : K*(C*(F*W)) ≤ (C+1)*F*constantHeatNormFactor α B := by
    calc
      _ = (C*(F*W))*K := by ring
      _ ≤ ((C+1)*(F*W))*(R*V) := mul_le_mul
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1) hFW)
        (hKR.trans hRV) hK (by positivity)
      _ = _ := by dsimp [constantHeatNormFactor,W,R,V,K]; ring
  have hHessBudget : K^2*(C*(F*W)) ≤ (C+1)*F*constantHeatNormFactor α B := by
    calc
      _ = (C*(F*W))*K^2 := by ring
      _ ≤ ((C+1)*(F*W))*(R*V) := mul_le_mul
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1) hFW)
        (hK2R.trans hRV) (sq_nonneg _) (by positivity)
      _ = _ := by dsimp [constantHeatNormFactor,W,R,V,K]; ring
  have hD := hDer T (F*W) hT (spaceTimePullback B f) hg p.2 hp.2 (B.symm p.1)
  have hFun : constantHeatDuhamel B f =
      spaceTimePullback B.symm (fun q => heatDuhamel (spaceTimePullback B f) q.2 q.1) := rfl
  refine ⟨?_,?_,?_⟩
  · exact (heatDuhamel_bound_of_holder hα hT hg hp.2 (B.symm p.1)).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hBudget hp.2.1])
  · rw [hFun,spatialD_spaceTimePullback]
    calc
      _ ≤ K*‖spatialD (fun q => heatDuhamel (spaceTimePullback B f) q.2 q.1)
          (B.symm p.1,p.2)‖ := gradientPullback_norm_le _ _
      _ ≤ K*(C*(F*W)*p.2^(1/2:ℝ)) := mul_le_mul_of_nonneg_left hD.1 hK
      _ = (K*(C*(F*W)))*p.2^(1/2:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hGradBudget (Real.rpow_nonneg hp.2.1 _)
  · rw [hFun,spatialDD_spaceTimePullback]
    calc
      _ ≤ K^2*‖spatialDD (fun q => heatDuhamel (spaceTimePullback B f) q.2 q.1)
          (B.symm p.1,p.2)‖ := hessianPullback_norm_le _ _
      _ ≤ K^2*(C*(F*W)*p.2^(α/2)) := mul_le_mul_of_nonneg_left hD.2 (sq_nonneg _)
      _ = (K^2*(C*(F*W)))*p.2^(α/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hHessBudget (Real.rpow_nonneg hp.2.1 _)

/-- The first-jet Hölder bound gains a positive power of the slab length. -/
theorem constantHeatDuhamel_first_jet_holderBound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Space n ≃L[ℝ] Space n) (T F : ℝ),
      0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      HolderBound α (cylinder Set.univ 0 T)
        (fun p : Point n => (constantHeatDuhamel B f p,spatialD (constantHeatDuhamel B f) p))
        (C*F*constantHeatNormFactor α B*(T^(1/2:ℝ)+T^((1-α)/2))) := by
  obtain ⟨C,hC,hJet⟩ := heatDuhamel_first_jet_holderBound (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro B T F hT hT1 f hf
  have hg := holderBound_comp_spaceLinearMap hα.le (B : Space n →L[ℝ] Space n) hf
  have hJ := hJet T _ hT hT1 (spaceTimePullback B f) hg
  have hComp := holderBound_comp_continuousLinearMap (firstJetPullback B.symm)
    (holderBound_comp_spaceLinearMap hα.le
      (B.symm : Space n →L[ℝ] Space n) hJ)
  have hNorm := firstJetPullback_norm_le B.symm
  have hBudget := mul_le_mul_of_nonneg_right hNorm
    (mul_nonneg hJ.1 (by positivity : 0 ≤ 1+‖(B.symm : Space n →L[ℝ] Space n)‖^α))
  have hBound := holderBound_mono_const hComp hBudget
  have hFun : constantHeatDuhamel B f =
      spaceTimePullback B.symm (fun q => heatDuhamel (spaceTimePullback B f) q.2 q.1) := rfl
  have hEq : Set.EqOn
      (fun p : Point n => firstJetPullback B.symm
        (heatDuhamel (spaceTimePullback B f) p.2 (B.symm p.1),
          spatialD (fun q => heatDuhamel (spaceTimePullback B f) q.2 q.1) (B.symm p.1,p.2)))
      (fun p : Point n => (constantHeatDuhamel B f p,spatialD (constantHeatDuhamel B f) p))
      (cylinder Set.univ 0 T) := by
    intro p hp
    dsimp only
    rw [hFun,spatialD_spaceTimePullback]
    rfl
  have hFinal := holderBound_congr_on hBound hEq
  convert hFinal using 1
  dsimp [constantHeatNormFactor]
  ring

end Yau.LeafProofs.L16Aux
