import Yau.LeafProofs.L17LocalizedSchauderProductBudget
import Yau.LeafProofs.L17LocalizedSchauderUnitSource

open Set Metric
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def transportJetBudget (k : ℕ) (C D gamma : ℝ) : ℝ :=
  8*(1+‖ContinuousLinearMap.mul ℝ ℝ‖)*(1+C)*compositionJetBudget k D gamma

theorem transportJetBudget_pos (k : ℕ) {C D gamma : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    0 < transportJetBudget k C D gamma := by
  unfold transportJetBudget
  exact mul_pos (mul_pos (mul_pos (by norm_num)
    (by positivity)) (by positivity)) (compositionJetBudget_pos k hD)

/-- A local composition and the genuine cutoff have uniform finite jet bounds
and near-point differences. Every input concerns the actual local functions. -/
theorem cutoff_composition_pair_bounds (P : UniformChartPartition g) (T : ℝ)
    (hρone : P.radius ≤ 1) (hρr : 2*P.radius < P.charts.radius)
    (p : P.centers) (q : M.Carrier) (k : ℕ) (hk : k ≤ 2)
    {C D F gamma : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hF : 0 ≤ F)
    (hγ : 0 < gamma) (hγone : gamma ≤ 1)
    (f : Time T → ComplexVector n → ℝ)
    (hf : ∀ t, ContDiffOn ℝ (k : ℕ∞ω) (f t) (ball (0 : ComplexVector n) 2))
    (hNorm : ∀ t z, z ∈ ball (0 : ComplexVector n) 2 → ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j (f t) z‖ ≤ F)
    (hDiff : ∀ t s z w, z ∈ ball (0 : ComplexVector n) 2 → w ∈ ball 0 2 → ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j (f t) z-iteratedFDeriv ℝ j (f s) w‖ ≤
        F*(unitParabolicDistance P.radius (z,t) (w,s))^gamma)
    (hCut : ∀ z ∈ ball (0 : ComplexVector n) 2, ∀ j, j ≤ k+1 →
      ‖iteratedFDeriv ℝ j (unitCutoff P p q) z‖ ≤ C)
    (hTransition :
      let a : ChartScaleIndex M := (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))
      (∀ z, z ∈ P.charts.scaledTransitionDomain a → ∀ j, j ≤ k →
        ‖iteratedFDeriv ℝ j (P.charts.scaledTransitionMap a) z‖ ≤ D) ∧
      ∀ z w, segment ℝ z w ⊆ P.charts.scaledTransitionDomain a → ∀ j, j ≤ k →
        ‖iteratedFDeriv ℝ j (P.charts.scaledTransitionMap a) w-
          iteratedFDeriv ℝ j (P.charts.scaledTransitionMap a) z‖ ≤ D*‖w-z‖)
    {z w : ComplexVector n} (hz : z ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (hSegment :
      let a : ChartScaleIndex M := (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))
      segment ℝ z w ⊆ P.charts.scaledTransitionDomain a)
    (t s : Time T) (hNear : unitParabolicDistance P.radius (z,t) (w,s) ≤ 1) :
    let a : ChartScaleIndex M := (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))
    ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j (fun x => unitCutoff P p q x*f t (P.charts.scaledTransitionMap a x)) z‖ ≤
        transportJetBudget k C D gamma*F ∧
      ‖iteratedFDeriv ℝ j (fun x => unitCutoff P p q x*f t (P.charts.scaledTransitionMap a x)) z-
        iteratedFDeriv ℝ j (fun x => unitCutoff P p q x*f s (P.charts.scaledTransitionMap a x)) w‖ ≤
        transportJetBudget k C D gamma*F*(unitParabolicDistance P.radius (z,t) (w,s))^gamma := by
  dsimp only
  let a : ChartScaleIndex M := (⟨P.radius,P.radius_pos,hρone⟩,(q,(p : M.Carrier)))
  let τ := P.charts.scaledTransitionMap a
  let U : Set (ComplexVector n) := ball 0 2 ∩ P.charts.scaledTransitionDomain a
  let d := unitParabolicDistance P.radius (z,t) (w,s)
  let K := compositionJetBudget k D gamma
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hK : 0 ≤ K := (compositionJetBudget_pos k hD0).le
  have hd : 0 ≤ d := unitParabolicDistance_nonneg P.radius_pos (z,t) (w,s)
  have hdpow : 0 ≤ d^gamma := Real.rpow_nonneg hd _
  have hSpace : ‖z-w‖ ≤ d := unitParabolicDistance_space_le P.radius_pos (z,t) (w,s)
  have hLinear : ‖z-w‖ ≤ d^gamma := hSpace.trans (self_le_rpow_on_unit hd hNear hγ hγone)
  have hzD : z ∈ P.charts.scaledTransitionDomain a := hSegment (left_mem_segment ℝ z w)
  have hwD : w ∈ P.charts.scaledTransitionDomain a := hSegment (right_mem_segment ℝ z w)
  have hz2 : z ∈ ball (0 : ComplexVector n) 2 := ball_subset_ball (by norm_num) hz
  have hw2 : w ∈ ball (0 : ComplexVector n) 2 := ball_subset_ball (by norm_num) hw
  have hzU : z ∈ U := ⟨hz2,hzD⟩
  have hwU : w ∈ U := ⟨hw2,hwD⟩
  have hU : IsOpen U := isOpen_ball.inter (P.charts.scaledTransitionDomain_isOpen a)
  have hτ : ContDiffOn ℝ ∞ τ U := (P.charts.scaledTransition_smooth a).mono inter_subset_right
  have hMap : MapsTo τ U (ball (0 : ComplexVector n) 2) := fun x hx => hx.2.2
  have hzt : τ z ∈ ball (0 : ComplexVector n) 2 := hMap hzU
  have hwt : τ w ∈ ball (0 : ComplexVector n) 2 := hMap hwU
  have hLip : ‖τ z-τ w‖ ≤ D*‖z-w‖ :=
    scaled_transition_value_lipschitz P.charts a (hTransition.2 z w hSegment 0 (Nat.zero_le k))
  have hPower : unitParabolicDistance P.radius (τ z,t) (τ w,s)^gamma ≤ D^gamma*d^gamma :=
    unitParabolicDistance_map_rpow_le P.radius_pos hD hγ.le τ (z,t) (w,s) hLip
  have hBudget (j : ℕ) (hj : j ≤ k) :
      2*‖ContinuousLinearMap.mul ℝ ℝ‖*bilinearJetConstant j*C*K ≤ transportJetBudget k C D gamma := by
    have hB := bilinearJetConstant_le_four (hj.trans hk)
    have hBn := bilinearJetConstant_nonneg j
    have hMul := norm_nonneg (ContinuousLinearMap.mul ℝ ℝ)
    dsimp only [transportJetBudget]
    change 2*‖ContinuousLinearMap.mul ℝ ℝ‖*bilinearJetConstant j*C*K ≤
      8*(1+‖ContinuousLinearMap.mul ℝ ℝ‖)*(1+C)*K
    calc
      2*‖ContinuousLinearMap.mul ℝ ℝ‖*bilinearJetConstant j*C*K ≤
          2*‖ContinuousLinearMap.mul ℝ ℝ‖*4*C*K := by gcongr
      _ = 8*‖ContinuousLinearMap.mul ℝ ℝ‖*C*K := by ring
      _ ≤ _ := by gcongr <;> linarith
  intro j hj
  have hτj : ContDiffOn ℝ (j : ℕ∞ω) τ U := hτ.of_le (by simp)
  have hfj (r : Time T) : ContDiffOn ℝ (j : ℕ∞ω) (f r ∘ τ) U :=
    ((hf r).of_le (by exact_mod_cast hj)).comp hτj hMap
  have hχj : ContDiffOn ℝ (j : ℕ∞ω) (unitCutoff P p q) U :=
    ((unitCutoff_contDiffOn P hρr p q).of_le (by simp)).mono inter_subset_left
  have hCompNorm (r : Time T) (x : ComplexVector n) (hx : x ∈ U) :
      ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i (f r ∘ τ) x‖ ≤ K*F := by
    intro i hi
    have hik := hi.trans hj
    have h := norm_iteratedFDeriv_comp_le_linear i
      (((hf r).of_le (by exact_mod_cast hik)).contDiffAt (isOpen_ball.mem_nhds (hMap hx)))
      ((hτ.of_le (by simp)).contDiffAt (hU.mem_nhds hx)) hF hD0
      (fun l hl => hNorm r (τ x) (hMap hx) l (hl.trans hik))
      (fun l hl => hTransition.1 x hx.2 l (hl.trans hik))
    exact h.trans (mul_le_mul_of_nonneg_right (compositionJetBudget_order_le hD0 hik).1 hF)
  have hCompDiff : ∀ i, i ≤ j →
      ‖iteratedFDeriv ℝ i (f t ∘ τ) z-iteratedFDeriv ℝ i (f s ∘ τ) w‖ ≤ K*F*d^gamma := by
    intro i hi
    have hik := hi.trans hj
    apply norm_iteratedFDeriv_comp_sub_le_factored k i hik
      (((hf t).of_le (by exact_mod_cast hik)).contDiffAt (isOpen_ball.mem_nhds hzt))
      (((hf s).of_le (by exact_mod_cast hik)).contDiffAt (isOpen_ball.mem_nhds hwt))
      ((hτ.of_le (by simp)).contDiffAt (hU.mem_nhds hzU))
      ((hτ.of_le (by simp)).contDiffAt (hU.mem_nhds hwU)) hF hD0 hdpow
      (fun l hl => hNorm t (τ z) hzt l (hl.trans hik))
      (fun l hl => (hDiff t s (τ z) (τ w) hzt hwt l (hl.trans hik)).trans
        ((mul_le_mul_of_nonneg_left hPower hF).trans_eq (by ring)))
      (fun l hl => hTransition.1 z hzD l (hl.trans hik))
      (fun l hl => hTransition.1 w hwD l (hl.trans hik))
      (fun l hl => by
        rw [norm_sub_rev]
        exact (hTransition.2 z w hSegment l (hl.trans hik)).trans
          (mul_le_mul_of_nonneg_left ((norm_sub_rev w z).le.trans hLinear) hD0))
  have hCutDelta : ∀ i, i ≤ j →
      ‖iteratedFDeriv ℝ i (unitCutoff P p q) z-iteratedFDeriv ℝ i (unitCutoff P p q) w‖ ≤ C*d^gamma := by
    intro i hi
    exact (unitCutoff_iteratedFDeriv_sub_le P hρr p q
      (fun x hx => hCut x hx (i+1) (by omega)) hz2 hw2).trans
        (mul_le_mul_of_nonneg_left hLinear hC)
  constructor
  · have hSup := norm_iteratedFDeriv_bilinear_le j (ContinuousLinearMap.mul ℝ ℝ) hU _ _
      hχj (hfj t) hzU hC (mul_nonneg hK hF)
      (fun i hi => hCut z hz2 i ((hi.trans hj).trans (Nat.le_succ k))) (hCompNorm t z hzU)
    have hB : ‖ContinuousLinearMap.mul ℝ ℝ‖*bilinearJetConstant j*C*K ≤ transportJetBudget k C D gamma := by
      have hn : 0 ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖*bilinearJetConstant j*C*K :=
        mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg (ContinuousLinearMap.mul ℝ ℝ)) (bilinearJetConstant_nonneg j)) hC) hK
      nlinarith [hBudget j hj]
    exact hSup.trans (by convert mul_le_mul_of_nonneg_right hB hF using 1 <;> ring)
  · have hSub := norm_iteratedFDeriv_product_sub_le_factored j (ContinuousLinearMap.mul ℝ ℝ) hU
      (unitCutoff P p q) (f t ∘ τ) (f s ∘ τ) hχj (hfj t) (hfj s) hzU hwU hC hK hF hdpow
      (fun i hi => hCut z hz2 i ((hi.trans hj).trans (Nat.le_succ k)))
      (hCompNorm s w hwU) hCutDelta hCompDiff
    exact hSub.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hBudget j hj) hF) hdpow)

end Yau.LeafProofs.L17LocalizedSchauderAux
