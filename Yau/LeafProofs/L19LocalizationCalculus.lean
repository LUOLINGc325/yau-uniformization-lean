import Yau.LeafProofs.L19LocalizationMaximum
import Yau.LeafProofs.L19MaximumAlgebra

/-! C² pointwise product calculus for the true spatial operators. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem chartRealLaplacian_mul (g : SmoothMetric M) (hK : IsKahler g)
    (a : M.Carrier) {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hz : z ∈ chartTarget a) (hf : ContDiffAt ℝ 2 f z) (hk : ContDiffAt ℝ 2 k z) :
    chartRealLaplacian g.form a (fun w => f w * k w) z =
      f z * chartRealLaplacian g.form a k z + k z * chartRealLaplacian g.form a f z +
        2 * chartGradientPair g.form a f k z := by
  rw [chartRealLaplacian_eq_principal g hK a hz,
    chartRealLaplacian_eq_principal g hK a hz,
    chartRealLaplacian_eq_principal g hK a hz]
  simp only [L18Aux.rDeriv_rDeriv_eq_hessian (hf.mul hk),
    L18Aux.rDeriv_rDeriv_eq_hessian hf, L18Aux.rDeriv_rDeriv_eq_hessian hk]
  rw [principal_secondFDeriv_mul _ hf hk,
    ← chartGradientPair_eq_sum, ← chartGradientPair_eq_sum,
    chartGradientPair_symm g.form a k f z]
  ring

theorem chartRealLaplacian_nonpos_at_local_max (g : SmoothMetric M) (q : M.Carrier)
    {f : ComplexVector n → ℝ} (hf : ContDiffAt ℝ 2 f (chartPt q q))
    (hm : IsLocalMax f (chartPt q q)) :
    chartRealLaplacian g.form q f (chartPt q q) ≤ 0 := by
  rw [chartRealLaplacian_eq_orthonormal_covHessian g.form q hf
    (realInitialOrthonormalFrame g q)]
  exact endpointFrameHessianTrace_nonpos_at_local_max g q _ hf hm

theorem chartGradientPair_zero_at_local_max (h : HermitianField M) (a : M.Carrier)
    {f : ComplexVector n → ℝ} {z : ComplexVector n} (hm : IsLocalMax f z)
    (k : ComplexVector n → ℝ) : chartGradientPair h a k f z = 0 := by
  simp only [chartGradientPair_eq_sum, rDeriv, hm.fderiv_eq_zero,
    zero_apply, mul_zero, Finset.sum_const_zero]

theorem chartGradientPair_product_at_local_max (h : HermitianField M) (a : M.Carrier)
    {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hk : DifferentiableAt ℝ k z)
    (hm : IsLocalMax (fun w => f w * k w) z) (v : ComplexVector n → ℝ) :
    f z * chartGradientPair h a v k z + k z * chartGradientPair h a v f z = 0 := by
  have hh := chartGradientPair_zero_at_local_max h a hm v
  rw [chartGradientPair_symm h a v _ z, chartGradientPair_mul_left h a v hf hk,
    chartGradientPair_symm h a k v z, chartGradientPair_symm h a f v z] at hh
  exact hh

theorem kahler_realLaplacian_center_eq (g : SmoothMetric M) (hK : IsKahler g)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (q : M.Carrier) :
    chartRealLaplacian g.form q (inChart q f) (chartPt q q) = 2 * laplacian g.form f q := by
  have hh := kahler_realLaplacian_on g hK hf q (mem_extChartAt_target q)
  simpa only [chartInv, chartPt, (extChartAt (ComplexModel n) q).left_inv
    (mem_extChartAt_source q)] using hh

/-- At a genuine positive maximum, the true C² cutoff calculus and
parabolic evolution give the strict Li--Yau numerical maximum bound. -/
theorem liYau_bound_at_positive_maximum (g : SmoothMetric M) (hK : IsKahler g)
    (hn : 0 < n) {f F η : M.Carrier → ℝ} (hf : SmoothFn f) (hF : SmoothFn F)
    (q : M.Carrier) {α s R d : ℝ} (hα : 1 < α) (hs : 0 < s) (hR : 0 < R)
    (hη : ContDiffAt ℝ 2 (inChart q η) (chartPt q q))
    (hηpos : 0 < η q) (hηone : η q ≤ 1) (hFpos : 0 < F q) (hd : 0 ≤ d)
    (hmax : IsLocalMax (fun z => inChart q η z * inChart q F z) (chartPt q q))
    (hηgrad : chartGradientPair g.form q (inChart q η) (inChart q η) (chartPt q q) ≤
      16 / R ^ 2 * η q)
    (hηlap : -(8 * (n : ℝ)) / R ^ 2 ≤
      chartRealLaplacian g.form q (inChart q η) (chartPt q q) / 2)
    (hD : laplacian g.form F q - d + scalarGradientPair g.form f F q ≥
      (F q + (α - 1) * s * gradNormSq g.form f q) ^ 2 /
        ((n : ℝ) * α ^ 2 * s) - F q / s) :
    η q * F q ≤ (n : ℝ) * α ^ 2 *
      (1 + s * (8 * (n : ℝ) + 16 + 4 * (n : ℝ) * α ^ 2 / (α - 1)) / R ^ 2) := by
  let z := chartPt q q
  let e := η q
  let A := F q
  let Q := gradNormSq g.form f q
  let B := chartGradientPair g.form q (inChart q η) (inChart q F) z
  let E := chartGradientPair g.form q (inChart q η) (inChart q η) z
  let Z := chartGradientPair g.form q (inChart q f) (inChart q η) z
  let L := chartRealLaplacian g.form q (inChart q η) z / 2
  let G := e * A
  let X := e * s * Q
  let w := s * Z
  have hz : z ∈ chartTarget q := mem_extChartAt_target q
  have hf2 : ContDiffAt ℝ 2 (inChart q f) z := (contDiffAt_inChart hf q hz).of_le (by simp)
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
    (hη.differentiableAt (by norm_num)) (hF2.differentiableAt (by norm_num)) hmax (inChart q f)
  rw [hηval, hFval] at hzero
  change e * scalarGradientPair g.form f F q + A * Z = 0 at hzero
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
  have hupper : e * (laplacian g.form F q + scalarGradientPair g.form f F q) ≤
      A * (8 * (n : ℝ) + 16) / R ^ 2 - A * Z := by
    have hh := mul_le_mul_of_nonneg_left hηlap hFpos.le
    change A * (-(8 * (n : ℝ)) / R ^ 2) ≤ A * L at hh
    have hsum : -A * L - B ≤ A * (8 * (n : ℝ) + 16) / R ^ 2 := by
      calc
        _ ≤ -(A * (-(8 * (n : ℝ)) / R ^ 2)) + 16 * A / R ^ 2 :=
          by convert add_le_add (neg_le_neg hh) hcross using 1 <;> ring
        _ = A * (8 * (n : ℝ) + 16) / R ^ 2 := by ring
    nlinarith only [hprod', hzero, hsum]
  have hlocal : e * ((A + (α - 1) * s * Q) ^ 2 /
      ((n : ℝ) * α ^ 2 * s) - A / s) ≤
      A * (8 * (n : ℝ) + 16) / R ^ 2 - A * Z := by
    have hh := mul_le_mul_of_nonneg_left hD hηpos.le
    have hnonneg := mul_nonneg hηpos.le hd
    change e * ((A + (α - 1) * s * Q) ^ 2 /
      ((n : ℝ) * α ^ 2 * s) - A / s) ≤
      e * (laplacian g.form F q - d + scalarGradientPair g.form f F q) at hh
    nlinarith only [hh, hupper, hnonneg]
  have hQ : 0 ≤ Q := by
    have hh := scalarGradientPair_self_nonneg g.form f q
    rw [scalarGradientPair_eq_twice_gradNormSq g.form hf q] at hh
    dsimp [Q]
    linarith
  have hCS := chartGradientPair_cauchySchwarz g.form q hz (inChart q f) (inChart q η)
  change Z ^ 2 ≤ scalarGradientPair g.form f f q * E at hCS
  rw [scalarGradientPair_eq_twice_gradNormSq g.form hf q] at hCS
  have hCS' : Z ^ 2 ≤ 2 * Q * (16 / R ^ 2 * e) :=
    hCS.trans (mul_le_mul_of_nonneg_left hηgrad (mul_nonneg (by norm_num) hQ))
  have hw : w ^ 2 ≤ 32 * s * X / R ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hCS' (sq_nonneg s)
    convert hh using 1 <;> dsimp [w, X] <;> ring
  have hG : 0 < G := mul_pos hηpos hFpos
  have hX : 0 ≤ X := mul_nonneg (mul_nonneg hηpos.le hs.le) hQ
  have hα0 := (lt_trans zero_lt_one hα).ne'
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hscaled := mul_le_mul_of_nonneg_left hlocal (mul_nonneg hηpos.le hs.le)
  have hlhs : (e * s) * (e * ((A + (α - 1) * s * Q) ^ 2 /
      ((n : ℝ) * α ^ 2 * s) - A / s)) =
      (G + (α - 1) * X) ^ 2 / ((n : ℝ) * α ^ 2) - e * G := by
    dsimp [G, X]
    field_simp
    <;> ring
  have hrhs : (e * s) * (A * (8 * (n : ℝ) + 16) / R ^ 2 - A * Z) =
      s * G * (8 * (n : ℝ) + 16) / R ^ 2 - G * w := by dsimp [G, w]; ring
  rw [hlhs, hrhs] at hscaled
  have heG : e * G ≤ G := by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hηone hG.le
  have hnumeric : (G + (α - 1) * X) ^ 2 / ((n : ℝ) * α ^ 2) - G -
      s * G * (8 * (n : ℝ) + 16) / R ^ 2 + G * w ≤ 0 := by
    linarith
  exact liYau_maximum_algebra (Nat.cast_pos.mpr hn) hα hs hR hG hX hw hnumeric

end Yau.LeafProofs.L19Aux
