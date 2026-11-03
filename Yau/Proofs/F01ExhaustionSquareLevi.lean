import Yau.Proofs.F01ConformalLeviBound
import Yau.Proofs.F01LaplacianLinearity

/-! The original dual gradient and Levi bounds control the actual square
of the exhaustion, with one constant before every point. -/
noncomputable section
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem square_scalar_levi_sandwich (g : HermitianField M)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) {C : ℝ} (hC : 0 ≤ C)
    (hpositive : ∀ x, 0 < u x)
    (hgradient : ∀ x, gradNormSq g u x ≤ C ^ 2)
    (hlevi : ∀ x,
      (levi u x - ((-(C / u x) : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      (((C / u x : ℝ) : ℂ) • gMat g x - levi u x).PosSemidef) :
    ∀ x,
      (levi (fun y => u y ^ 2) x - ((-(2 * C + 2 * C ^ 2) : ℝ) : ℂ) •
        gMat g x).PosSemidef ∧
      (((2 * C + 2 * C ^ 2 : ℝ) : ℂ) • gMat g x -
        levi (fun y => u y ^ 2) x).PosSemidef := by
  intro x
  let z : ComplexVector n := chartPt x x
  have hux : inChart x u z = u x := by simp [z, inChart, chartInv, chartPt]
  have hu2 : ContDiffAt ℝ 2 (inChart x u) z := smoothFn_chart_contDiffAt hu x
  have hH : (gMat g x).PosDef :=
    LeafProofs.L12Aux.hMat_posDef g x z (mem_extChartAt_target x)
  have hF : ContDiffAt ℝ 2 (fun s : ℝ => s ^ 2) (inChart x u z / 1) := by fun_prop
  have hd : deriv (fun s : ℝ => s ^ 2) = fun s => 2 * s := by
    funext s
    simpa using ((hasDerivAt_id s).pow 2).deriv
  have hdd : deriv (deriv (fun s : ℝ => s ^ 2)) = fun _ => 2 := by
    rw [hd]
    funext s
    simpa using ((hasDerivAt_id s).const_mul 2).deriv
  change (leviC (fun w => inChart x u w ^ 2) z - _).PosSemidef ∧
    (_ - leviC (fun w => inChart x u w ^ 2) z).PosSemidef
  apply leviC_sandwich_of_quadratic _ hH.isHermitian (hu2.pow 2)
  intro v
  have hquad := leviC_quadratic_abs_of_sandwich (gMat g x) hH.isHermitian hu2
    (C / u x) (hlevi x).1 (hlevi x).2
  have hm := scaled_scalar_levi_quadratic_bound (gMat g x) hH
    (L := 1) (by norm_num) hu2 hF (hgradient x) hquad v
  have hc : |2 * u x| * (C / u x) + |(2 : ℝ)| * C ^ 2 =
      2 * C + 2 * C ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (hpositive x).le)]
    norm_num
    field_simp [(hpositive x).ne']
    <;> ring
  rw [hdd, hd] at hm
  simp only [div_one, one_pow] at hm
  rw [hux, hc] at hm
  exact hm

theorem controlled_exhaustion_square_levi (X : KahlerManifold n)
    (o : Yau.Blueprint.Pt X) (u : Yau.Blueprint.Pt X → ℝ)
    (hu : Yau.Blueprint.ControlledExhaustion X o u) :
    ∃ K : ℝ, 0 < K ∧ ∀ x,
      (levi (fun y => u y ^ 2) x - ((-K : ℝ) : ℂ) • gMat X.metric.form x).PosSemidef ∧
      ((K : ℂ) • gMat X.metric.form x - levi (fun y => u y ^ 2) x).PosSemidef := by
  obtain ⟨C, hC, hc⟩ := hu.2.2.2
  refine ⟨2 * C + 2 * C ^ 2, by positivity, ?_⟩
  apply square_scalar_levi_sandwich X.metric.form u hu.1 hC.le
    (fun x => lt_of_lt_of_le zero_lt_one (hu.2.2.1 x))
    (fun x => (hc x).2.2.1)
  intro x
  constructor
  · simpa only [Yau.Blueprint.HermLE, Complex.ofReal_neg, Complex.ofReal_div] using
      (hc x).2.2.2.1
  · exact (hc x).2.2.2.2

end Yau.NodeProofs.F01Aux
