import Yau.LeafProofs.L24Bernstein

/-! Actual C² support maximum estimates for the Bernstein energy. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L24Aux
open L12Aux L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

theorem bernstein_maximum_algebra {β B G s R w : ℝ}
    (hβ : 0 < β) (hG : 0 < G) (hs : 0 < s) (hR : 0 < R)
    (hw : w ^ 2 ≤ 8 * s * G / R ^ 2)
    (hineq : β * G ≤ 1 + B * s / R ^ 2 + w) :
    G ≤ (2 / β) * (1 + (B + 4 / β) * s / R ^ 2) := by
  let a := β * G / 2
  let b := 4 * s / (β * R ^ 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have heq : 8 * s * G / R ^ 2 = 4 * a * b := by
    dsimp [a, b]
    field_simp
    ring
  have hw' : w ^ 2 ≤ 4 * a * b := by rwa [heq] at hw
  have hYoung : w ≤ a + b := by nlinarith [sq_nonneg (a-b)]
  have hbase : β * G / 2 ≤ 1 + B * s / R ^ 2 + b := by
    dsimp [a] at hYoung
    linarith
  have hmul := mul_le_mul_of_nonneg_left hbase (le_of_lt (div_pos (by norm_num) hβ) : 0 ≤ 2 / β)
  have hleft : (2 / β) * (β * G / 2) = G := by field_simp
  rw [hleft] at hmul
  convert hmul using 1
  dsimp [b]
  ring

theorem bernstein_bound_at_positive_maximum
    (g : SmoothMetric M) (hK : IsKahler g)
    {v F η : M.Carrier → ℝ} (hv : SmoothFn v) (hF : SmoothFn F)
    (q : M.Carrier) {β s R dt : ℝ}
    (hβ : 0 < β) (hs : 0 < s) (hR : 0 < R)
    (hη : ContDiffAt ℝ 2 (inChart q η) (chartPt q q))
    (hηpos : 0 < η q) (hηone : η q ≤ 1)
    (hFpos : 0 < F q) (hdt : 0 ≤ dt)
    (hunit : v q ^ 2 ≤ 1)
    (henergy : s * gradNormSq g.form v q ≤ F q)
    (hmax : IsLocalMax (fun z => inChart q η z * inChart q F z) (chartPt q q))
    (hηgrad : chartGradientPair g.form q (inChart q η) (inChart q η)
      (chartPt q q) ≤ 16 / R ^ 2 * η q)
    (hηlap : -(8 * (n : ℝ)) / R ^ 2 ≤
      chartRealLaplacian g.form q (inChart q η) (chartPt q q) / 2)
    (hD : β * F q ^ 2 / s + (v q / 2) * scalarGradientPair g.form v F q - F q / s ≤
      laplacian g.form F q - dt) :
    η q * F q ≤ (2 / β) *
      (1 + (8 * (n : ℝ) + 16 + 4 / β) * s / R ^ 2) := by
  let z := chartPt q q
  let e := η q
  let A := F q
  let Q := gradNormSq g.form v q
  let B := chartGradientPair g.form q (inChart q η) (inChart q F) z
  let E := chartGradientPair g.form q (inChart q η) (inChart q η) z
  let Z₀ := chartGradientPair g.form q (inChart q v) (inChart q η) z
  let Z := (v q / 2) * Z₀
  let L := chartRealLaplacian g.form q (inChart q η) z / 2
  let G := e * A
  let w := s * Z
  have hz : z ∈ chartTarget q := mem_extChartAt_target q
  have hF2 : ContDiffAt ℝ 2 (inChart q F) z := (contDiffAt_inChart hF q hz).of_le (by simp)
  have hηval : inChart q η z = e :=
    congrArg η ((extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q))
  have hFval : inChart q F z = A :=
    congrArg F ((extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q))
  have hprod := chartRealLaplacian_nonpos_at_local_max g q (hη.mul hF2) hmax
  rw [chartRealLaplacian_mul g hK q hz hη hF2, hηval, hFval,
    kahler_realLaplacian_center_eq g hK hF q] at hprod
  have hprod' : e * laplacian g.form F q + A * L + B ≤ 0 := by
    dsimp [L, B]
    linarith
  have hzero := chartGradientPair_product_at_local_max g.form q
    (hη.differentiableAt (by norm_num)) (hF2.differentiableAt (by norm_num)) hmax (inChart q v)
  rw [hηval, hFval] at hzero
  change e * scalarGradientPair g.form v F q + A * Z₀ = 0 at hzero
  have hzeroη := chartGradientPair_product_at_local_max g.form q
    (hη.differentiableAt (by norm_num)) (hF2.differentiableAt (by norm_num)) hmax (inChart q η)
  rw [hηval, hFval] at hzeroη
  change e * B + A * E = 0 at hzeroη
  have hcross : -B ≤ 16 * A / R ^ 2 := by
    apply (mul_le_mul_iff_left₀ hηpos).mp
    have hh := mul_le_mul_of_nonneg_left hηgrad hFpos.le
    change -B * e ≤ (16 * A / R ^ 2) * e
    change A * E ≤ A * (16 / R ^ 2 * e) at hh
    calc
      -B * e = A * E := by nlinarith only [hzeroη]
      _ ≤ A * (16 / R ^ 2 * e) := hh
      _ = (16 * A / R ^ 2) * e := by ring
  have hupper : e * laplacian g.form F q ≤ A * (8 * (n : ℝ) + 16) / R ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hηlap hFpos.le
    change A * (-(8 * (n : ℝ)) / R ^ 2) ≤ A * L at hh
    have hsum : -A * L - B ≤ A * (8 * (n : ℝ) + 16) / R ^ 2 := by
      calc
        _ ≤ -(A * (-(8 * (n : ℝ)) / R ^ 2)) + 16 * A / R ^ 2 :=
          by convert add_le_add (neg_le_neg hh) hcross using 1; ring
        _ = A * (8 * (n : ℝ) + 16) / R ^ 2 := by ring
    linarith only [hsum, hprod']
  have hlocal : e * (β * A ^ 2 / s - A / s) ≤
      A * (8 * (n : ℝ) + 16) / R ^ 2 + A * Z := by
    have hh := mul_le_mul_of_nonneg_left hD hηpos.le
    have hnonneg := mul_nonneg hηpos.le hdt
    have hzero' := congrArg (fun r : ℝ => (v q / 2) * r) hzero
    dsimp [Z]
    change e * (β * A ^ 2 / s + (v q / 2) * scalarGradientPair g.form v F q - A / s) ≤
      e * (laplacian g.form F q - dt) at hh
    nlinarith only [hh, hupper, hnonneg, hzero']
  have hscaled := mul_le_mul_of_nonneg_left hlocal hs.le
  have heq : s * (e * (β * A ^ 2 / s - A / s)) = A * (β * G - e) := by
    dsimp [G]
    field_simp
  rw [heq] at hscaled
  have hnumeric : β * G ≤ 1 + (8 * (n : ℝ) + 16) * s / R ^ 2 + w := by
    have hcancel : A * (β * G - e) ≤ A * ((8 * (n : ℝ) + 16) * s / R ^ 2 + w) := by
      convert hscaled using 1
      dsimp [w]
      ring
    have hh := (mul_le_mul_iff_right₀ hFpos).mp hcancel
    dsimp [e] at hh
    linarith
  have hQ : 0 ≤ Q := gradNormSq_nonneg g.form hv q
  have hE : 0 ≤ E := chartGradientPair_self_nonneg g.form q hz (inChart q η)
  have hCS := chartGradientPair_cauchySchwarz g.form q hz (inChart q v) (inChart q η)
  change Z₀ ^ 2 ≤ scalarGradientPair g.form v v q * E at hCS
  rw [scalarGradientPair_eq_twice_gradNormSq g.form hv q] at hCS
  have hCS' : Z ^ 2 ≤ Q * E / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hCS (div_nonneg (sq_nonneg (v q)) (by norm_num : (0:ℝ) ≤ 4))
    have h2 := mul_le_mul_of_nonneg_right hunit (mul_nonneg hQ hE)
    dsimp [Z]
    nlinarith only [h1, h2]
  have hCS'' : Z ^ 2 ≤ 8 * Q * e / R ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hηgrad hQ
    change Q * E ≤ Q * (16 / R ^ 2 * e) at hh
    calc
      Z ^ 2 ≤ Q * E / 2 := hCS'
      _ ≤ (Q * (16 / R ^ 2 * e)) / 2 := div_le_div_of_nonneg_right hh (by norm_num)
      _ = 8 * Q * e / R ^ 2 := by ring
  have hw : w ^ 2 ≤ 8 * s * G / R ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hCS'' (sq_nonneg s)
    have he := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 8 * s * e / R ^ 2)
    change (8 * s * e / R ^ 2) * (s * Q) ≤ (8 * s * e / R ^ 2) * A at he
    dsimp only [w, G]
    calc
      (s * Z) ^ 2 ≤ (8 * s * e / R ^ 2) * (s * Q) := by
        convert hh using 1 <;> ring
      _ ≤ (8 * s * e / R ^ 2) * A := he
      _ = 8 * s * (e * A) / R ^ 2 := by ring
  exact bernstein_maximum_algebra hβ (mul_pos hηpos hFpos) hs hR hw hnumeric

end Yau.LeafProofs.L24Aux
