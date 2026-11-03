import Yau.Proofs.P07SupportWeakScalar
import Yau.Proofs.P06LeviTests
import Yau.LeafProofs.L22Second
import Yau.LeafProofs.L22Circle

noncomputable section
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
namespace Yau.NodeProofs.P07Aux.SupportWeak
open Yau Yau.Blueprint Yau.LeafProofs L18Aux L22Aux P06Aux
variable {n : ℕ}

/-- Only one fixed direction is controlled, and the support is a genuine C² germ. -/
def LocalDirectionalUpperSupportsOn (O : Set (ComplexVector n))
    (f h : ComplexVector n → ℝ) (v : ComplexVector n) : Prop :=
  ∀ z ∈ O, ∃ S : ComplexVector n → ℝ, ContDiffAt ℝ 2 S z ∧
    S z = f z ∧ (∀ᶠ w in 𝓝 z, f w ≤ S w) ∧
    leviDirection (leviC S z) v ≤ h z

def LineLowerTestUpperOn (O : Set (ComplexVector n))
    (f : ComplexVector n → ℝ) (v : ComplexVector n)
    (h : ComplexVector n → ℝ) : Prop :=
  ∀ a z, a + z • v ∈ O → ∀ q : ℂ → ℝ,
    ContDiffAt ℝ 2 q z → q z = f (a + z • v) →
    (∀ᶠ ζ in 𝓝 z, q ζ ≤ f (a + ζ • v)) →
    complexLap q z ≤ 4 * h (a + z • v)

/-- The affine complex line has no second derivative; no direction normalization occurs. -/
theorem complexLap_affine_comp {S : ComplexVector n → ℝ}
    (a v : ComplexVector n) (z : ℂ)
    (hS : ContDiffAt ℝ 2 S (a + z • v)) :
    complexLap (fun ζ : ℂ => S (a + ζ • v)) z =
      4 * leviDirection (leviC S (a + z • v)) v := by
  let l : ℂ →L[ℝ] ComplexVector n :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight v).restrictScalars ℝ
  have hl (ζ : ℂ) : l ζ = ζ • v := rfl
  have hd (ζ : ℂ) : fderiv ℝ (fun ζ : ℂ => a + ζ • v) ζ = l :=
    (l.hasFDerivAt.const_add a).fderiv
  have hdd : fderiv ℝ (fderiv ℝ (fun ζ : ℂ => a + ζ • v)) z = 0 := by
    rw [show fderiv ℝ (fun ζ : ℂ => a + ζ • v) = fun _ => l from funext hd]
    simp
  have hs : ContDiffAt ℝ 2 (fun ζ : ℂ => a + ζ • v) z :=
    contDiffAt_const.add l.contDiff.contDiffAt
  rw [complexLap_eq_hessian, show (fun ζ : ℂ => S (a + ζ • v)) =
    S ∘ (fun ζ : ℂ => a + ζ • v) from rfl,
    secondFDeriv_comp hs hS, secondFDeriv_comp hs hS, hd, hdd]
  simp only [hl, one_smul, ContinuousLinearMap.zero_apply, map_zero, add_zero]
  rw [leviDirection_eq_second hS, directionSecond_eq_hessian hS,
    directionSecond_eq_hessian hS]
  ring

theorem complexLap_nonneg_of_localMin {q : ℂ → ℝ} {z : ℂ}
    (hq : ContDiffAt ℝ 2 q z) (hmin : IsLocalMin q z) : 0 ≤ complexLap q z := by
  rw [complexLap_eq_hessian]
  exact add_nonneg (hessian_nonneg_of_localMin hq hmin 1)
    (hessian_nonneg_of_localMin hq hmin Complex.I)

/-- Restrict the actual upper support before comparing it with a scalar lower test. -/
theorem complexLap_lowerTest_of_upperSupport
    {f S : ComplexVector n → ℝ} {a v : ComplexVector n} {z : ℂ} {q : ℂ → ℝ}
    (hS : ContDiffAt ℝ 2 S (a + z • v))
    (hSf : ∀ᶠ w in 𝓝 (a + z • v), f w ≤ S w)
    (hSz : S (a + z • v) = f (a + z • v))
    (hq : ContDiffAt ℝ 2 q z) (hqz : q z = f (a + z • v))
    (hqf : ∀ᶠ ζ in 𝓝 z, q ζ ≤ f (a + ζ • v)) :
    complexLap q z ≤ 4 * leviDirection (leviC S (a + z • v)) v := by
  have hc : Continuous (fun ζ : ℂ => a + ζ • v) := by fun_prop
  have hs : ContDiffAt ℝ 2 (fun ζ : ℂ => S (a + ζ • v)) z :=
    hS.comp z (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have hmin : IsLocalMin (fun ζ : ℂ => S (a + ζ • v) - q ζ) z := by
    filter_upwards [hc.continuousAt.eventually hSf, hqf] with ζ hζ hζ'
    change S (a + z • v) - q z ≤ S (a + ζ • v) - q ζ
    rw [hSz, hqz, sub_self]
    exact sub_nonneg.mpr (hζ'.trans hζ)
  have hn := complexLap_nonneg_of_localMin (hs.sub hq) hmin
  rw [complexLap_sub hs hq, complexLap_affine_comp a v z hS] at hn
  linarith

theorem lineLowerTests_of_localUpperSupports
    {O : Set (ComplexVector n)} {f h : ComplexVector n → ℝ} {v : ComplexVector n}
    (hs : LocalDirectionalUpperSupportsOn O f h v) : LineLowerTestUpperOn O f v h := by
  intro a z hz q hq hqz hqf
  obtain ⟨S, hS, hSz, hSf, hSb⟩ := hs _ hz
  exact (complexLap_lowerTest_of_upperSupport hS hSf hSz hq hqz hqf).trans
    (mul_le_mul_of_nonneg_left hSb (by norm_num))

theorem leviDirection_real_smul {S : ComplexVector n → ℝ} {z : ComplexVector n}
    (hS : ContDiffAt ℝ 2 S z) (v : ComplexVector n) (r : ℝ) :
    leviDirection (leviC S z) (r • v) = r ^ 2 * leviDirection (leviC S z) v := by
  simp only [leviDirection, leviC_quadratic_re hS,
    complexLeviQuadratic_smul]

/-- The two circle-average definitions agree after the explicit circle-map normalization. -/
theorem circleAverage_eq_yau (k : ℂ → ℝ) :
    Real.circleAverage k 0 1 = Yau.circleAverage (fun θ => k (Complex.exp (θ * Complex.I))) := by
  simp [Real.circleAverage, Yau.circleAverage, circleMap, smul_eq_mul]

/-- The signed radius enters quadratically, with no sign condition on b. -/
theorem angularLineMean_le_of_localUpperSupports
    {O : Set (ComplexVector n)} {f h : ComplexVector n → ℝ} {v a : ComplexVector n}
    (hf : ContinuousOn f O) (hs : LocalDirectionalUpperSupportsOn O f h v)
    (r b : ℝ) (hdisc : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → a + ζ • (r • v) ∈ O)
    (hh : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → h (a + ζ • (r • v)) ≤ b) :
    angularLineMean f a v r ≤ f a + b * r ^ 2 := by
  have hg : ContinuousOn (fun ζ : ℂ => f (a + ζ • (r • v))) (closedBall 0 1) := by
    apply hf.comp (by fun_prop)
    intro ζ hζ
    exact hdisc ζ (by simpa only [mem_closedBall, dist_zero_right] using hζ)
  have ht : ScalarLowerTestUpperOn (ball 0 1)
      (fun ζ : ℂ => f (a + ζ • (r • v))) (4 * (b * r ^ 2)) := by
    intro z hz q hq hqz hqf
    have hz' : ‖z‖ ≤ 1 := by simpa only [mem_ball, dist_zero_right] using (mem_ball.mp hz).le
    obtain ⟨S, hS, hSz, hSf, hSb⟩ := hs _ (hdisc z hz')
    have hle := complexLap_lowerTest_of_upperSupport hS hSf hSz hq hqz hqf
    rw [leviDirection_real_smul hS] at hle
    have hb := hSb.trans (hh z hz')
    nlinarith [sq_nonneg r, mul_le_mul_of_nonneg_left hb (sq_nonneg r)]
  have hm := circleSupermean_of_lowerTests_const hg ht
  rw [circleAverage_eq_yau] at hm
  simpa only [angularLineMean, zero_smul, add_zero, smul_comm r] using hm

end Yau.NodeProofs.P07Aux.SupportWeak
