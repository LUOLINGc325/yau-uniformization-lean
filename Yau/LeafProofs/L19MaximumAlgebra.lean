import Yau.LeafProofs.L19Limits

/-! The numerical maximum argument for the strict Li--Yau coefficient.
The drift estimate follows from its squared Cauchy--Schwarz bound, so no
uncontrolled sign of a time derivative enters the argument. -/

noncomputable section

namespace Yau.LeafProofs.L19Aux

theorem lower_bound_of_sq_le_four_mul {z U V : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hz : z ^ 2 ≤ 4 * U * V) :
    -(U + V) ≤ z := by
  by_contra h
  have hlt : z < -(U + V) := lt_of_not_ge h
  have hpos : 0 < -z := by linarith
  have hsquare : (U + V) ^ 2 < z ^ 2 := by
    have hh := mul_self_lt_mul_self (add_nonneg hU hV) (by linarith : U + V < -z)
    nlinarith
  nlinarith [sq_nonneg (U - V)]

/-- Absorbing the drift uses exactly the cross term of the main square. -/
theorem liYau_maximum_square_bound {M A G X b e z : ℝ}
    (hM : 0 < M) (hA : 0 < A) (hG : 0 < G) (hX : 0 ≤ X) (he : 0 ≤ e)
    (hz : z ^ 2 ≤ 4 * e * X)
    (hmax : (G + A * X) ^ 2 / M - G * (1 + b) + G * z ≤ 0) :
    G ≤ M * (1 + b + M * e / (2 * A)) := by
  let U := 2 * A * X / M
  let V := M * e / (2 * A)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hprod : 4 * U * V = 4 * e * X := by
    dsimp [U, V]
    field_simp
  have hYoung : -(U + V) ≤ z :=
    lower_bound_of_sq_le_four_mul hU hV (by rwa [hprod])
  have hmain : (G + A * X) ^ 2 ≤ M * (G * (1 + b) - G * z) := by
    have hh : (G + A * X) ^ 2 / M ≤ G * (1 + b) - G * z := by linarith
    simpa only [mul_comm] using (div_le_iff₀ hM).mp hh
  have hdrift : -M * G * z ≤ M * G * (U + V) := by
    have hh := mul_le_mul_of_nonneg_left (neg_le_neg hYoung)
      (mul_nonneg hM.le hG.le)
    nlinarith
  have hmain' : (G + A * X) ^ 2 ≤ M * G * (1 + b + U + V) := by
    nlinarith [hmain, hdrift]
  have hcross : M * G * U = 2 * A * G * X := by
    dsimp [U]
    field_simp
  have hsq : G * G ≤ (M * (1 + b + V)) * G := by
    nlinarith [hmain', hcross, sq_nonneg (A * X)]
  apply (mul_le_mul_iff_right₀ hG).mp
  simpa only [V, mul_comm] using hsq

/-- Numerical conclusion at a positive maximum of η·s·(Q−α f_t),
using the genuine complex normalization P(f,f)=2Q. -/
theorem liYau_maximum_algebra {d α s R G X z : ℝ}
    (hd : 0 < d) (hα : 1 < α) (hs : 0 < s) (hR : 0 < R)
    (hG : 0 < G) (hX : 0 ≤ X)
    (hz : z ^ 2 ≤ 32 * s * X / R ^ 2)
    (hmax : (G + (α - 1) * X) ^ 2 / (d * α ^ 2) - G -
      s * G * (8 * d + 16) / R ^ 2 + G * z ≤ 0) :
    G ≤ d * α ^ 2 *
      (1 + s * (8 * d + 16 + 4 * d * α ^ 2 / (α - 1)) / R ^ 2) := by
  have hαpos : 0 < α := lt_trans zero_lt_one hα
  have hA : 0 < α - 1 := sub_pos.mpr hα
  have hbound := liYau_maximum_square_bound
    (M := d * α ^ 2) (A := α - 1) (G := G) (X := X)
    (b := s * (8 * d + 16) / R ^ 2) (e := 8 * s / R ^ 2) (z := z)
    (by positivity) hA hG hX (by positivity)
    (by convert hz using 1; ring)
    (by convert hmax using 1; ring)
  convert hbound using 1
  field_simp
  ring

end Yau.LeafProofs.L19Aux
