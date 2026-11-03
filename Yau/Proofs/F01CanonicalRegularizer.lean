import Yau.Proofs.P08CanonicalLogRicci
import Yau.Proofs.P08LogRegularizer

/-! Smooth canonical logarithms retaining the full Ricci lower bound. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.LeafProofs Yau.Proofs.P04Aux Yau.NodeProofs.P08Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- The positive term uses the same smooth majorant as the initial potential. -/
def canonicalRegularizer (g : SmoothMetric M) (S : CanonicalSection M)
    (Ξ : M.Carrier → ℝ) (δ : ℝ) : M.Carrier → ℝ :=
  fun x => Real.log (canonicalNormSq g.form S x + δ * Real.exp (Ξ x))

theorem canonicalRegularizer_smooth (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) (Ξ : M.Carrier → ℝ) (hΞ : SmoothFn Ξ)
    {δ : ℝ} (hδ : 0 < δ) : SmoothFn (canonicalRegularizer g S Ξ δ) := by
  intro a
  exact ((canonicalNormSq_smooth g S hS a).add
    (contDiffOn_const.mul (hΞ a).exp)).log
    (fun z _ => (add_pos_of_nonneg_of_pos (canonicalNormSq_nonneg g.form S _)
      (mul_pos hδ (Real.exp_pos _))).ne')

/-- Factoring out the positive majorant is valid even at a zero of the section. -/
theorem canonicalRegularizer_eq_split (g : SmoothMetric M) (S : CanonicalSection M)
    (Ξ : M.Carrier → ℝ) {δ : ℝ} (hδ : 0 < δ) (x : M.Carrier) :
    canonicalRegularizer g S Ξ δ x =
      Ξ x + Real.log (canonicalNormSq g.form S x * Real.exp (-Ξ x) + δ) := by
  have hp : 0 < canonicalNormSq g.form S x * Real.exp (-Ξ x) + δ :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg (canonicalNormSq_nonneg g.form S x) (Real.exp_pos _).le) hδ
  have heq : canonicalNormSq g.form S x + δ * Real.exp (Ξ x) =
      Real.exp (Ξ x) * (canonicalNormSq g.form S x * Real.exp (-Ξ x) + δ) := by
    symm
    calc
      _ = canonicalNormSq g.form S x * (Real.exp (Ξ x) * Real.exp (-Ξ x)) +
          δ * Real.exp (Ξ x) := by ring
      _ = _ := by rw [← Real.exp_add]; simp
  rw [canonicalRegularizer, heq, Real.log_mul (Real.exp_ne_zero _) hp.ne', Real.log_exp]

/-- A smooth maximum of two potentials preserves a common Levi lower bound. -/
theorem leviC_add_logRegularizer_lower {f h : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hh : ContDiffAt ℝ 2 h z)
    (hLower : HermLE (leviC f z) (leviC h z)) {δ : ℝ} (hδ : 0 < δ) :
    HermLE (leviC f z)
      (leviC (fun w => h w + logRegularizer δ (f w + (-1) * h w)) z) := by
  let v := fun w => f w + (-1) * h w
  have hv : ContDiffAt ℝ 2 v z := hf.add (contDiffAt_const.mul hh)
  have hF : ContDiffAt ℝ 2 (logRegularizer δ) (v z) :=
    (logRegularizer_contDiff hδ).contDiffAt.of_le (by simp)
  have hcoef : 0 ≤ 1 - deriv (logRegularizer δ) (v z) := by
    rw [logRegularizer_deriv hδ]
    exact sub_nonneg.mpr ((div_le_one (add_pos (Real.exp_pos _) hδ)).mpr
      (le_add_of_nonneg_right hδ.le))
  have hp := (show (leviC h z - leviC f z).PosSemidef from hLower).smul
    (Complex.zero_le_real.mpr hcoef)
  have hgram := (gradientGram_posSemidef v z).smul
    (Complex.zero_le_real.mpr (logRegularizer_deriv_deriv_nonneg hδ (v z)))
  have hcomp : ContDiffAt ℝ 2 (fun w => logRegularizer δ (v w)) z := hF.comp z hv
  change (leviC (fun w => h w + logRegularizer δ (v w)) z - leviC f z).PosSemidef
  rw [L17Aux.leviC_add hh hcomp, leviC_scalar_comp hv hF]
  have hlevi : leviC v z = leviC f z + ((-1 : ℝ) : ℂ) • leviC h z :=
    (L17Aux.leviC_add hf (contDiffAt_const.mul hh)).trans
      (congrArg (fun A => leviC f z + A) (L17Aux.leviC_const_mul hh (-1)))
  rw [hlevi]
  convert hp.add hgram using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg]
  ring

/-- This lower bound holds at every point, including every zero of the section,
and in every complex dimension. -/
theorem canonicalRegularizer_levi_lower (g : SmoothMetric M) (S : CanonicalSection M)
    (hS : IsHolomorphicCanonical S) (Ξ : M.Carrier → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, HermLE (ricci g.form x) (levi Ξ x)) {δ : ℝ} (hδ : 0 < δ)
    (x : M.Carrier) :
    HermLE (ricci g.form x) (levi (canonicalRegularizer g S Ξ δ) x) := by
  let q := canonicalNormSq g.form S
  let r : M.Carrier → ℝ := fun y => Real.log (q y * Real.exp (-Ξ y) + δ)
  let z := chartPt x x
  have hz : z ∈ chartTarget x := mem_extChartAt_target x
  have hx : chartInv x z = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hq : SmoothFn q := canonicalNormSq_smooth g S hS
  have hr : SmoothFn r := by
    intro a
    exact (((hq a).mul ((hΞ a).neg.exp)).add contDiffOn_const).log
      (fun w _ => (add_pos_of_nonneg_of_pos
        (mul_nonneg (canonicalNormSq_nonneg g.form S _) (Real.exp_pos _).le) hδ).ne')
  have hΞ2 : ContDiffAt ℝ 2 (inChart x Ξ) z :=
    (L18Aux.contDiffAt_inChart hΞ x hz).of_le (by simp)
  have hr2 : ContDiffAt ℝ 2 (inChart x r) z :=
    (L18Aux.contDiffAt_inChart hr x hz).of_le (by simp)
  have hsplit : inChart x (canonicalRegularizer g S Ξ δ) =
      fun w => inChart x Ξ w + inChart x r w := by
    funext w
    exact canonicalRegularizer_eq_split g S Ξ hδ _
  by_cases hzero : q x = 0
  · have hmin : IsLocalMin (inChart x r) z := by
      apply Filter.Eventually.of_forall
      intro w
      change Real.log (q (chartInv x z) * Real.exp (-Ξ (chartInv x z)) + δ) ≤ _
      rw [hx, hzero, zero_mul, zero_add]
      exact Real.log_le_log hδ (le_add_of_nonneg_left
        (mul_nonneg (canonicalNormSq_nonneg g.form S _) (Real.exp_pos _).le))
    have hp := leviC_posSemidef_at_local_min hr2 hmin
    change (leviC (inChart x (canonicalRegularizer g S Ξ δ)) z - ricci g.form x).PosSemidef
    rw [hsplit, L17Aux.leviC_add hΞ2 hr2]
    have hricpsd : (leviC (inChart x Ξ) z - ricci g.form x).PosSemidef := hRic x
    convert hricpsd.add hp using 1
    abel
  · have hpos : 0 < q x :=
      lt_of_le_of_ne (canonicalNormSq_nonneg g.form S x) (Ne.symm hzero)
    have hqz : inChart x q z = q x := congrArg q hx
    have hlog : ContDiffAt ℝ 2 (fun w => Real.log (inChart x q w)) z :=
      ((L18Aux.contDiffAt_inChart hq x hz).of_le (by simp)).log
        (by rw [hqz]; exact hpos.ne')
    have hRicEq : leviC (fun w => Real.log (inChart x q w)) z = ricci g.form x :=
      levi_log_canonicalNormSq_at_pos g S hS x hpos
    have hLower : HermLE (leviC (fun w => Real.log (inChart x q w)) z)
        (leviC (inChart x Ξ) z) := by
      rw [hRicEq]
      exact hRic x
    have hp := leviC_add_logRegularizer_lower hlog hΞ2 hLower hδ
    have heq :
        (fun w => inChart x Ξ w + logRegularizer δ
          (Real.log (inChart x q w) + (-1) * inChart x Ξ w)) =ᶠ[𝓝 z]
        inChart x (canonicalRegularizer g S Ξ δ) := by
      filter_upwards [(L18Aux.contDiffAt_inChart hq x hz).continuousAt.eventually
        (Ioi_mem_nhds (by rw [hqz]; exact hpos))] with w hw
      rw [hsplit]
      change _ = inChart x Ξ w + Real.log (inChart x q w * Real.exp (-inChart x Ξ w) + δ)
      simp only [logRegularizer, neg_one_mul, Real.exp_add, Real.exp_log hw]
    rw [L22Aux.leviC_congr_of_eventuallyEq heq, hRicEq] at hp
    exact hp

end Yau.NodeProofs.F01Aux
