import Yau.LeafProofs.L16ClassicalCutoff

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem c2_spatialD_lipschitz_on_closedBall {n : ℕ} {R l r K : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder (Metric.closedBall 0 R) l r) u)
    (hK : ∀ p ∈ cylinder (Metric.closedBall 0 R) l r, ‖spatialDD u p‖ ≤ K)
    {t : ℝ} (ht : t ∈ Set.Icc l r) {x y : Space n}
    (hx : x ∈ Metric.closedBall 0 R) (hy : y ∈ Metric.closedBall 0 R) :
    ‖spatialD u (x,t)-spatialD u (y,t)‖ ≤ K*‖x-y‖ := by
  have hDiff (z : Space n) (hz : z ∈ Metric.closedBall 0 R) :
      DifferentiableAt ℝ (fun w => spatialD u (w,t)) z := by
    change DifferentiableAt ℝ (fderiv ℝ (fun w => u (w,t))) z
    exact ((hu.2.2.2.2.1 (z,t) ⟨hz,ht⟩).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hBound (z : Space n) (hz : z ∈ Metric.closedBall 0 R) :
      ‖fderiv ℝ (fun w => spatialD u (w,t)) z‖ ≤ K := hK (z,t) ⟨hz,ht⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hDiff hBound
    (convex_closedBall (0 : Space n) R) hy hx

theorem c2_time_lipschitz_on_closedBall {n : ℕ} {R l r K : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder (Metric.closedBall 0 R) l r) u)
    (hK : ∀ p ∈ cylinder (Metric.closedBall 0 R) l r,
      |timeD (cylinder (Metric.closedBall 0 R) l r) u p| ≤ K)
    {x : Space n} (hx : x ∈ Metric.closedBall 0 R)
    {s t : ℝ} (hs : s ∈ Set.Icc l r) (ht : t ∈ Set.Icc l r) :
    |u (x,t)-u (x,s)| ≤ K*|t-s| := by
  have hSlice : {v : ℝ | (x,v) ∈ cylinder (Metric.closedBall (0 : Space n) R) l r} =
      Set.Icc l r := by
    ext v
    simp [Yau.Parabolic.cylinder,hx]
  have hDeriv (v : ℝ) (hv : v ∈ Set.Icc l r) :
      HasDerivWithinAt (fun z => u (x,z))
        (timeD (cylinder (Metric.closedBall 0 R) l r) u (x,v)) (Set.Icc l r) v := by
    simpa only [timeD,hSlice] using (hu.2.2.2.2.2 (x,v) ⟨hx,hv⟩).hasDerivWithinAt
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hDeriv
      (fun v hv => hK (x,v) ⟨hx,hv⟩) (convex_Icc l r) hs ht

/-- A local secant estimate obtained from the actual Hessian, without
    requiring differentiability outside the larger closed ball. -/
theorem c2_directional_taylor_remainder {n : ℕ} {R l r K s ℓ : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder (Metric.closedBall 0 R) l r) u)
    (hK : ∀ p ∈ cylinder (Metric.closedBall 0 R) l r, ‖spatialDD u p‖ ≤ K)
    (hK0 : 0 ≤ K) (hℓ : 0 < ℓ) (hMargin : s+ℓ ≤ R)
    {t : ℝ} (ht : t ∈ Set.Icc l r) {x : Space n} (hx : x ∈ Metric.closedBall 0 s)
    (e : Space n) (he : ‖e‖ ≤ 1) :
    |u (x+ℓ • e,t)-u (x,t)-ℓ*spatialD u (x,t) e| ≤ K*ℓ^2 := by
  let G : Space n →L[ℝ] ℝ := spatialD u (x,t)
  let g : Space n → ℝ := fun y => u (y,t)-G y
  have hxNorm : ‖x‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hSub : Metric.closedBall x ℓ ⊆ Metric.closedBall (0 : Space n) R := by
    intro y hy
    have hyNorm : ‖y-x‖ ≤ ℓ := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
    rw [Metric.mem_closedBall,dist_zero_right]
    have hTri := norm_add_le (y-x) x
    rw [sub_add_cancel] at hTri
    linarith
  have hxR : x ∈ Metric.closedBall (0 : Space n) R :=
    hSub (Metric.mem_closedBall_self hℓ.le)
  have hDiff (y : Space n) (hy : y ∈ Metric.closedBall x ℓ) :
      DifferentiableAt ℝ g y :=
    ((hu.2.2.2.2.1 (y,t) ⟨hSub hy,ht⟩).differentiableAt (by norm_num)).sub G.differentiableAt
  have hDeriv (y : Space n) (hy : y ∈ Metric.closedBall x ℓ) :
      fderiv ℝ g y = spatialD u (y,t)-G := by
    simpa only [spatialD,ContinuousLinearMap.fderiv] using
      fderiv_fun_sub ((hu.2.2.2.2.1 (y,t) ⟨hSub hy,ht⟩).differentiableAt
        (by norm_num)) G.differentiableAt
  have hBound (y : Space n) (hy : y ∈ Metric.closedBall x ℓ) :
      ‖fderiv ℝ g y‖ ≤ K*ℓ := by
    rw [hDeriv y hy]
    have hLip := c2_spatialD_lipschitz_on_closedBall hu hK ht (hSub hy) hxR
    exact hLip.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy) hK0)
  have hEnd : x+ℓ • e ∈ Metric.closedBall x ℓ := by
    rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hℓ]
    nlinarith
  have hMean := Convex.norm_image_sub_le_of_norm_fderiv_le hDiff hBound
    (convex_closedBall x ℓ) (Metric.mem_closedBall_self hℓ.le) hEnd
  have hExpr : g (x+ℓ • e)-g x =
      u (x+ℓ • e,t)-u (x,t)-ℓ*spatialD u (x,t) e := by
    dsimp only [g]
    rw [G.map_add,G.map_smul]
    simp only [smul_eq_mul]
    ring
  rw [hExpr,Real.norm_eq_abs,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hℓ] at hMean
  exact hMean.trans (by nlinarith [mul_nonneg (mul_nonneg hK0 hℓ.le) hℓ.le])

theorem c2_directional_secant_bound {n : ℕ} {R l r K s ℓ : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder (Metric.closedBall 0 R) l r) u)
    (hK : ∀ p ∈ cylinder (Metric.closedBall 0 R) l r, ‖spatialDD u p‖ ≤ K)
    (hK0 : 0 ≤ K) (hℓ : 0 < ℓ) (hMargin : s+ℓ ≤ R)
    {t : ℝ} (ht : t ∈ Set.Icc l r) {x : Space n} (hx : x ∈ Metric.closedBall 0 s)
    (e : Space n) (he : ‖e‖ ≤ 1) :
    |spatialD u (x,t) e-(u (x+ℓ • e,t)-u (x,t))/ℓ| ≤ K*ℓ := by
  have hTaylor := c2_directional_taylor_remainder hu hK hK0 hℓ hMargin ht hx e he
  have hExpr : spatialD u (x,t) e-(u (x+ℓ • e,t)-u (x,t))/ℓ =
      -(u (x+ℓ • e,t)-u (x,t)-ℓ*spatialD u (x,t) e)/ℓ := by
    field_simp
    ring
  rw [hExpr,abs_div,abs_neg,abs_of_pos hℓ]
  calc
    _ ≤ (K*ℓ^2)/ℓ := div_le_div_of_nonneg_right hTaylor hℓ.le
    _ = K*ℓ := by field_simp

theorem c2_spatialD_sup_bound {n : ℕ} {R l r K B s ℓ : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder (Metric.closedBall 0 R) l r) u)
    (hK : ∀ p ∈ cylinder (Metric.closedBall 0 R) l r, ‖spatialDD u p‖ ≤ K)
    (hB : ∀ p ∈ cylinder (Metric.closedBall 0 R) l r, |u p| ≤ B)
    (hK0 : 0 ≤ K) (hB0 : 0 ≤ B) (hℓ : 0 < ℓ) (hMargin : s+ℓ ≤ R)
    {t : ℝ} (ht : t ∈ Set.Icc l r) {x : Space n} (hx : x ∈ Metric.closedBall 0 s) :
    ‖spatialD u (x,t)‖ ≤ K*ℓ+2*B/ℓ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (f := spatialD u (x,t)) (by positivity)
  intro e he
  have he1 : ‖e‖ ≤ 1 := he.le
  have hxR : x ∈ Metric.closedBall (0 : Space n) R :=
    Metric.closedBall_subset_closedBall (by linarith) hx
  have hEnd : x+ℓ • e ∈ Metric.closedBall (0 : Space n) R := by
    have hxNorm : ‖x‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    rw [Metric.mem_closedBall,dist_zero_right]
    have hTri := norm_add_le x (ℓ • e)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hℓ,he,mul_one] at hTri
    linarith
  have hDiff : |u (x+ℓ • e,t)-u (x,t)| ≤ 2*B := by
    calc
      _ ≤ |u (x+ℓ • e,t)|+|u (x,t)| := abs_sub _ _
      _ ≤ B+B := add_le_add (hB (x+ℓ • e,t) ⟨hEnd,ht⟩) (hB (x,t) ⟨hxR,ht⟩)
      _ = 2*B := by ring
  have hSecant := c2_directional_secant_bound hu hK hK0 hℓ hMargin ht hx e he1
  change |spatialD u (x,t) e| ≤ _
  calc
    _ = |(spatialD u (x,t) e-(u (x+ℓ • e,t)-u (x,t))/ℓ)+
        (u (x+ℓ • e,t)-u (x,t))/ℓ| := by congr 1; ring
    _ ≤ |spatialD u (x,t) e-(u (x+ℓ • e,t)-u (x,t))/ℓ|+
        |(u (x+ℓ • e,t)-u (x,t))/ℓ| := abs_add_le _ _
    _ ≤ K*ℓ+2*B/ℓ := by
      apply add_le_add hSecant
      rw [abs_div,abs_of_pos hℓ]
      exact div_le_div_of_nonneg_right hDiff hℓ.le

/-- The temporal half estimate for the gradient uses two spatial secants,
    and requires no mixed space-time derivative. -/
theorem c2_spatialD_temporal_half_bound {n : ℕ} {R l r K s ρ : ℝ}
    {u : Point n → ℝ} (hu : C2 (cylinder (Metric.closedBall 0 R) l r) u)
    (hHess : ∀ p ∈ cylinder (Metric.closedBall 0 R) l r, ‖spatialDD u p‖ ≤ K)
    (hTime : ∀ p ∈ cylinder (Metric.closedBall 0 R) l r,
      |timeD (cylinder (Metric.closedBall 0 R) l r) u p| ≤ K)
    (hK : 0 ≤ K) (hMargin : s+ρ ≤ R)
    {x : Space n} (hx : x ∈ Metric.closedBall 0 s)
    {t v : ℝ} (ht : t ∈ Set.Icc l r) (hv : v ∈ Set.Icc l r)
    (hSmall : Real.sqrt |t-v| ≤ ρ) :
    ‖spatialD u (x,t)-spatialD u (x,v)‖ ≤ 4*K*Real.sqrt |t-v| := by
  by_cases htv : t = v
  · subst t
    simp
  let ℓ : ℝ := Real.sqrt |t-v|
  have hℓ : 0 < ℓ := Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr htv))
  have hℓSq : ℓ^2 = |t-v| := Real.sq_sqrt (abs_nonneg _)
  have hMarginℓ : s+ℓ ≤ R := by linarith
  have hxR : x ∈ Metric.closedBall (0 : Space n) R :=
    Metric.closedBall_subset_closedBall (by linarith) hx
  apply ContinuousLinearMap.opNorm_le_of_unit_norm
    (f := spatialD u (x,t)-spatialD u (x,v)) (by positivity)
  intro e he
  have hEnd : x+ℓ • e ∈ Metric.closedBall (0 : Space n) R := by
    have hxNorm : ‖x‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
    rw [Metric.mem_closedBall,dist_zero_right]
    have hTri := norm_add_le x (ℓ • e)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hℓ,he,mul_one] at hTri
    linarith
  have hSecantT := c2_directional_secant_bound hu hHess hK hℓ hMarginℓ ht hx e he.le
  have hSecantV := c2_directional_secant_bound hu hHess hK hℓ hMarginℓ hv hx e he.le
  have hEndTime := c2_time_lipschitz_on_closedBall hu hTime hEnd hv ht
  have hBaseTime := c2_time_lipschitz_on_closedBall hu hTime hxR hv ht
  have hNumerator :
      |(u (x+ℓ • e,t)-u (x,t))-(u (x+ℓ • e,v)-u (x,v))| ≤ 2*K*|t-v| := by
    have hExpr : (u (x+ℓ • e,t)-u (x,t))-(u (x+ℓ • e,v)-u (x,v)) =
        (u (x+ℓ • e,t)-u (x+ℓ • e,v))-(u (x,t)-u (x,v)) := by ring
    rw [hExpr]
    exact (abs_sub _ _).trans ((add_le_add hEndTime hBaseTime).trans_eq (by ring))
  have hMiddle :
      |(u (x+ℓ • e,t)-u (x,t))/ℓ-(u (x+ℓ • e,v)-u (x,v))/ℓ| ≤ 2*K*ℓ := by
    rw [← sub_div,abs_div,abs_of_pos hℓ]
    calc
      _ ≤ (2*K*|t-v|)/ℓ := div_le_div_of_nonneg_right hNumerator hℓ.le
      _ = 2*K*ℓ := by rw [← hℓSq]; field_simp
  change |spatialD u (x,t) e-spatialD u (x,v) e| ≤ _
  calc
    _ = |(spatialD u (x,t) e-(u (x+ℓ • e,t)-u (x,t))/ℓ)+
        ((u (x+ℓ • e,t)-u (x,t))/ℓ-(u (x+ℓ • e,v)-u (x,v))/ℓ)+
        ((u (x+ℓ • e,v)-u (x,v))/ℓ-spatialD u (x,v) e)| := by congr 1; ring
    _ ≤ |spatialD u (x,t) e-(u (x+ℓ • e,t)-u (x,t))/ℓ|+
        |(u (x+ℓ • e,t)-u (x,t))/ℓ-(u (x+ℓ • e,v)-u (x,v))/ℓ|+
        |(u (x+ℓ • e,v)-u (x,v))/ℓ-spatialD u (x,v) e| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K*ℓ+2*K*ℓ+K*ℓ :=
      add_le_add (add_le_add hSecantT hMiddle) (by simpa only [abs_sub_comm] using hSecantV)
    _ = 4*K*Real.sqrt |t-v| := by dsimp only [ℓ]; ring

end Yau.LeafProofs.L16Aux
