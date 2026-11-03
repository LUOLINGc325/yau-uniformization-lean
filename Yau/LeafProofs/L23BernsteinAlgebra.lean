import Yau.LeafProofs.L23TensorCalculus

/-! The numerical part of the tensor Bernstein estimate. -/

noncomputable section

namespace Yau.LeafProofs.L23Aux

/-- The tensor Kato cross term is absorbed without an upper bound on w or z. -/
theorem bernstein_cross_absorption {B v w z q : ℝ}
    (hB : 0 ≤ B) (hv : 0 ≤ v) (hvB : v ≤ B) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hq : q ^ 2 ≤ 16 * v * w ^ 2 * z) :
    -q ≤ ((16*B+v)/2)*z + w^2/2 := by
  let s := ((16*B+v)/2)*z + w^2/2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hcoeff : 0 ≤ 16*B - 15*v := by linarith
  have hprod := mul_nonneg hcoeff (mul_nonneg (sq_nonneg w) hz)
  have hsq : 16*v*w^2*z ≤ s^2 := by
    dsimp [s]
    nlinarith [sq_nonneg (((16*B+v)/2)*z - w^2/2)]
  by_contra h
  have hlt : s < -q := lt_of_not_ge h
  have hh := mul_self_lt_mul_self hs hlt
  nlinarith

/-- The exact negative quadratic inequality for F=(16B+v)w. -/
theorem bernstein_negative_quadratic {B v w z σ Dk Ek pv pw q : ℝ}
    (hB : 1 ≤ B) (hv : 0 ≤ v) (hvB : v ≤ B) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hσ : 0 < σ) (hDk : 0 ≤ Dk) (hEk : 0 ≤ Ek)
    (hpv : pv ≤ -σ*w + σ*Ek)
    (hpw : pw ≤ -σ*z + σ*Dk*(1+w))
    (hq : q^2 ≤ 16*v*w^2*z) :
    (16*B+v)*pw + w*pv - σ*q ≤
      -σ / (4*(17*B)^2) * ((16*B+v)*w)^2 +
        σ*((17*B*Dk+Ek)^2 + 17*B*Dk) := by
  have hBpos : 0 < B := by linarith
  have hA : 0 ≤ 16*B+v := by positivity
  have hP : 0 < 17*B := by positivity
  have hF : 0 ≤ (16*B+v)*w := mul_nonneg hA hw
  have hFupper : (16*B+v)*w ≤ 17*B*w := by nlinarith
  have hF2 : ((16*B+v)*w)^2 ≤ (17*B)^2*w^2 := by
    have hh := mul_self_le_mul_self hF hFupper
    nlinarith
  have hc := bernstein_cross_absorption hBpos.le hv hvB hw hz hq
  have h1 := mul_le_mul_of_nonneg_left hpw hA
  have h2 := mul_le_mul_of_nonneg_left hpv hw
  have h3 := mul_le_mul_of_nonneg_left hc hσ.le
  have h4 : 0 ≤ σ*(16*B+v)*z/2 := by positivity
  have h5 : (16*B+v)*Dk*(1+w) ≤ 17*B*Dk*(1+w) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ 1+w)
    exact mul_le_mul_of_nonneg_right (by linarith) hDk
  have h6 := mul_le_mul_of_nonneg_left h5 hσ.le
  have hfirst : (16*B+v)*pw + w*pv - σ*q ≤
      -σ/2*w^2 + σ*(17*B*Dk+Ek)*w + σ*(17*B*Dk) := by
    nlinarith
  have hy := mul_nonneg hσ.le (sq_nonneg (w/2-(17*B*Dk+Ek)))
  have hsecond : (16*B+v)*pw + w*pv - σ*q ≤
      -σ/4*w^2 + σ*((17*B*Dk+Ek)^2+17*B*Dk) := by
    nlinarith [hfirst]
  have hden : 0 < 4*(17*B)^2 := by positivity
  have hlast : -σ/4*w^2 ≤ -σ/(4*(17*B)^2)*((16*B+v)*w)^2 := by
    apply (mul_le_mul_iff_right₀ hden).mp
    have hh := mul_le_mul_of_nonneg_left hF2 hσ.le
    field_simp
    nlinarith
  linarith

/-- A coarse explicit solution of the nonnegative quadratic maximum inequality. -/
theorem quadratic_maximum_bound {a b c W : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hW : 0 ≤ W)
    (hmax : a*W^2 ≤ b*W+c) :
    W ≤ 2*b/a + Real.sqrt (2*c/a) := by
  have hbdiv : 0 ≤ 2*b/a := by positivity
  have hsqrt : 0 ≤ Real.sqrt (2*c/a) := Real.sqrt_nonneg _
  have hsqrt2 : Real.sqrt (2*c/a)^2 = 2*c/a := Real.sq_sqrt (by positivity)
  by_contra h
  have hlt : 2*b/a + Real.sqrt (2*c/a) < W := lt_of_not_ge h
  have hWpos : 0 < W := lt_of_le_of_lt (add_nonneg hbdiv hsqrt) hlt
  have h1 : 2*b < a*W := by
    have hh : 2*b/a < W := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ ha).mp hh
  have h2 : Real.sqrt (2*c/a) < W := by linarith
  have h3 : Real.sqrt (2*c/a)^2 < W^2 := by
    nlinarith [mul_self_lt_mul_self hsqrt h2]
  have h4 : 2*c < a*W^2 := by
    have hh := mul_lt_mul_of_pos_left h3 ha
    have he : a*(2*c/a) = 2*c := by field_simp
    rw [hsqrt2, he] at hh
    exact hh
  have h5 := mul_lt_mul_of_pos_right h1 hWpos
  nlinarith

end Yau.LeafProofs.L23Aux
