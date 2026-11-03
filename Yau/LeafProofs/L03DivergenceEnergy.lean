import Yau.LeafProofs.L03DivergenceMollifier
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Filter
open scoped Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section
namespace Yau.LeafProofs.L03
namespace DivergenceEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure]

/-- Integration by parts for a compact smooth test and an arbitrary smooth field. -/
theorem compact_ibp (f g : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) (hg : ContDiff ℝ ∞ g) (v : E) :
    (∫ x, f x * fderiv ℝ g x v ∂ν) =
      -(∫ x, fderiv ℝ f x v * g x ∂ν) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := ν)
    ((hdf.mul hg.continuous).integrable_of_hasCompactSupport
      (hcf.fderiv_apply ℝ v).mul_right)
    ((hf.continuous.mul hdg).integrable_of_hasCompactSupport hcf.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcf.mul_right)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)

variable {α ι : Type*} [Fintype α] [Fintype ι]

def derivative (v : ι → E) (U : E → α → ℝ) (x : E) (p : ι × α) : ℝ :=
  fderiv ℝ (fun y => U y p.2) x (v p.1)

def valueSq (U : E → α → ℝ) (x : E) : ℝ := ∑ c, (U x c)^2

def gradientSq (v : ι → E) (U : E → α → ℝ) (x : E) : ℝ :=
  ∑ p, (derivative v U x p)^2

def principal (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (U : E → α → ℝ) (x : E) : ℝ :=
  ∑ r, ∑ c, ∑ i, ∑ j,
    a r c i j x * derivative v U x (j,c) * derivative v U x (i,r)

def flux (B : α → α → ι → E → ℝ) (U : E → α → ℝ)
    (x : E) (p : ι × α) : ℝ := ∑ c, B p.2 c p.1 x * U x c

def zeroth (C : α → α → E → ℝ) (U : E → α → ℝ) (x : E) : ℝ :=
  ∑ r, ∑ c, C r c x * U x c * U x r

theorem derivative_smooth (v : ι → E) (U : E → α → ℝ)
    (hU : ∀ c, ContDiff ℝ ∞ (fun x => U x c)) (p : ι × α) :
    ContDiff ℝ ∞ (fun x => derivative v U x p) :=
  ((hU p.2).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem derivative_compact (v : ι → E) (U : E → α → ℝ)
    (hcU : ∀ c, HasCompactSupport (fun x => U x c)) (p : ι × α) :
    HasCompactSupport (fun x => derivative v U x p) :=
  (hcU p.2).fderiv_apply ℝ (v p.1)

/-- Scalar Young inequality with the coercive parameter. -/
theorem young_two (ell : ℝ) (hell : 0 < ell) (b g d : ℝ) :
    b*d-g*d ≤ (ell/2)*d^2 + (1/ell)*(b^2+g^2) := by
  have h := add_nonneg (sq_nonneg (ell*d-2*b)) (sq_nonneg (ell*d+2*g))
  apply (mul_le_mul_iff_left₀ hell).mp
  field_simp
  nlinarith

/-- A finite matrix entry bound controls the actual flux; empty families are included. -/
theorem flux_sq_le (B : α → α → ι → E → ℝ) (U : E → α → ℝ)
    (x : E) (b : ℝ) (hb : 0 ≤ b)
    (hB : ∀ r c i, |B r c i x| ≤ b) (p : ι × α) :
    (flux B U x p)^2 ≤ (Fintype.card α : ℝ)*b^2*valueSq U x := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun c => B p.2 c p.1 x * U x c)
  simp only [Finset.card_univ] at hcs
  refine hcs.trans ?_
  have ht : (∑ c, (B p.2 c p.1 x * U x c)^2) ≤
      b^2 * ∑ c, (U x c)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hb).mpr (hB p.2 c p.1))
      (sq_nonneg _)
  have hn : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  simpa only [valueSq, mul_assoc] using mul_le_mul_of_nonneg_left ht hn

/-- The compact test integral commutes with a finite sum of continuous fields. -/
theorem test_sum {κ : Type*} [Fintype κ] (w : E → ℝ)
    (hw : Continuous w) (hcw : HasCompactSupport w)
    (h : κ → E → ℝ) (hh : ∀ k, Continuous (h k)) :
    (∫ x, w x * ∑ k, h k x ∂ν) = ∑ k, ∫ x, w x * h k x ∂ν := by
  classical
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ (fun k _ =>
    (hw.mul (hh k)).integrable_of_hasCompactSupport hcw.mul_right)

/-- Exact rowwise energy identity for the actual divergence operator. -/
theorem row_identity (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U : E → α → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hC : ∀ r c, Continuous (C r c))
    (hU : ∀ c, ContDiff ℝ ∞ (fun x => U x c))
    (hcU : ∀ c, HasCompactSupport (fun x => U x c)) (r : α) :
    (∫ x, U x r * divergenceSystemApply v a B C U x r ∂ν) =
      ∑ c, ((∑ i, ∑ j, ∫ x,
        a r c i j x * derivative v U x (j,c) * derivative v U x (i,r) ∂ν) -
        (∑ i, ∫ x, B r c i x * U x c * derivative v U x (i,r) ∂ν) +
        ∫ x, C r c x * U x c * U x r ∂ν) := by
  classical
  let A (c : α) (i j : ι) : E → ℝ :=
    fun x => a r c i j x * derivative v U x (j,c)
  let Q (c : α) (i : ι) : E → ℝ := fun x => B r c i x * U x c
  have hA (c : α) (i j : ι) : ContDiff ℝ ∞ (A c i j) :=
    (ha r c i j).mul (derivative_smooth v U hU (j,c))
  have hQ (c : α) (i : ι) : ContDiff ℝ ∞ (Q c i) := (hB r c i).mul (hU c)
  have hdA (c : α) (i j : ι) : Continuous
      (fun x => fderiv ℝ (A c i j) x (v i)) :=
    ((hA c i j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdQ (c : α) (i : ι) : Continuous
      (fun x => fderiv ℝ (Q c i) x (v i)) :=
    ((hQ c i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hsA (c : α) : Continuous (fun x => ∑ i, ∑ j,
      fderiv ℝ (A c i j) x (v i)) :=
    continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => hdA c i j))
  have hsQ (c : α) : Continuous (fun x => ∑ i, fderiv ℝ (Q c i) x (v i)) :=
    continuous_finsetSum _ (fun i _ => hdQ c i)
  have hZ (c : α) : Continuous (fun x => C r c x * U x c) :=
    (hC r c).mul (hU c).continuous
  change (∫ x, U x r * ∑ c, (-(∑ i, ∑ j,
    fderiv ℝ (A c i j) x (v i)) + (∑ i, fderiv ℝ (Q c i) x (v i)) +
      C r c x * U x c) ∂ν) = _
  rw [test_sum ν _ (hU r).continuous (hcU r)
    (fun c x => -(∑ i, ∑ j, fderiv ℝ (A c i j) x (v i)) +
      (∑ i, fderiv ℝ (Q c i) x (v i)) + C r c x * U x c)
    (fun c => ((hsA c).neg.add (hsQ c)).add (hZ c))]
  apply Finset.sum_congr rfl
  intro c _
  have hiA := ((hU r).continuous.mul (hsA c).neg).integrable_of_hasCompactSupport
    (hcU r).mul_right (μ := ν)
  have hiQ := ((hU r).continuous.mul (hsQ c)).integrable_of_hasCompactSupport
    (hcU r).mul_right (μ := ν)
  have hiZ := ((hU r).continuous.mul (hZ c)).integrable_of_hasCompactSupport
    (hcU r).mul_right (μ := ν)
  simp_rw [mul_add]
  rw [integral_add (f := fun x => U x r * (-(∑ i, ∑ j, fderiv ℝ (A c i j) x (v i))) +
      U x r * (∑ i, fderiv ℝ (Q c i) x (v i)))
      (g := fun x => U x r * (C r c x * U x c)) (hiA.add hiQ) hiZ,
    integral_add (f := fun x => U x r * (-(∑ i, ∑ j, fderiv ℝ (A c i j) x (v i))))
      (g := fun x => U x r * (∑ i, fderiv ℝ (Q c i) x (v i))) hiA hiQ]
  simp_rw [mul_neg, integral_neg]
  rw [test_sum ν _ (hU r).continuous (hcU r)
      (fun i x => ∑ j, fderiv ℝ (A c i j) x (v i))
      (fun i => continuous_finsetSum _ (fun j _ => hdA c i j)),
    test_sum ν _ (hU r).continuous (hcU r)
      (fun i x => fderiv ℝ (Q c i) x (v i)) (fun i => hdQ c i)]
  simp_rw [test_sum ν _ (hU r).continuous (hcU r)
    (fun j x => fderiv ℝ (A c _ j) x (v _)) (fun j => hdA c _ j)]
  simp_rw [compact_ibp ν _ _ (hU r) (hcU r) (hA c _ _) _,
    compact_ibp ν _ _ (hU r) (hcU r) (hQ c _) _, Finset.sum_neg_distrib]
  simp only [neg_neg, sub_eq_add_neg]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae (Filter.Eventually.of_forall _)
      intro x
      dsimp only [A, derivative]
      ring
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae (Filter.Eventually.of_forall _)
      intro x
      dsimp only [Q, derivative]
      ring
  · apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro x
    ring

/-- Testing the given pointwise residual uses only the smooth compact field. -/
theorem forcing_row (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U f : E → α → ℝ) (g : E → α → ι → ℝ)
    (hU : ∀ c, ContDiff ℝ ∞ (fun x => U x c))
    (hcU : ∀ c, HasCompactSupport (fun x => U x c))
    (hf : ∀ r, Continuous (fun x => f x r))
    (hg : ∀ r i, ContDiff ℝ ∞ (fun x => g x r i))
    (heq : ∀ x r, divergenceSystemApply v a B C U x r =
      f x r + ∑ i, fderiv ℝ (fun y => g y r i) x (v i)) (r : α) :
    (∫ x, U x r * divergenceSystemApply v a B C U x r ∂ν) =
      (∫ x, f x r * U x r ∂ν) -
      ∑ i, ∫ x, g x r i * derivative v U x (i,r) ∂ν := by
  classical
  have hdg (i : ι) : Continuous (fun x => fderiv ℝ (fun y => g y r i) x (v i)) :=
    ((hg r i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hsg : Continuous (fun x => ∑ i, fderiv ℝ (fun y => g y r i) x (v i)) :=
    continuous_finsetSum _ (fun i _ => hdg i)
  simp_rw [heq, mul_add]
  rw [integral_add (f := fun x => U x r * f x r)
      (g := fun x => U x r * ∑ i, fderiv ℝ (fun y => g y r i) x (v i))
      (((hU r).continuous.mul (hf r)).integrable_of_hasCompactSupport (hcU r).mul_right)
      (((hU r).continuous.mul hsg).integrable_of_hasCompactSupport (hcU r).mul_right),
    test_sum ν _ (hU r).continuous (hcU r)
      (fun i x => fderiv ℝ (fun y => g y r i) x (v i)) hdg]
  simp_rw [compact_ibp ν _ _ (hU r) (hcU r) (hg r _) _, Finset.sum_neg_distrib]
  simp only [sub_eq_add_neg]
  congr 1
  · apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro x
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae (Filter.Eventually.of_forall _)
    intro x
    simp only [derivative]
    ring

/-- The finite system energy identity, obtained from the actual pointwise PDE. -/
theorem energy_identity (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U f : E → α → ℝ) (g : E → α → ι → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hC : ∀ r c, Continuous (C r c))
    (hU : ∀ c, ContDiff ℝ ∞ (fun x => U x c))
    (hcU : ∀ c, HasCompactSupport (fun x => U x c))
    (hf : ∀ r, Continuous (fun x => f x r))
    (hg : ∀ r i, ContDiff ℝ ∞ (fun x => g x r i))
    (heq : ∀ x r, divergenceSystemApply v a B C U x r =
      f x r + ∑ i, fderiv ℝ (fun y => g y r i) x (v i)) :
    (∫ x, principal v a U x ∂ν) =
      (∫ x, ∑ r, f x r * U x r ∂ν) +
      (∫ x, ∑ p, flux B U x p * derivative v U x p ∂ν) -
      (∫ x, zeroth C U x ∂ν) -
      (∫ x, ∑ p, g x p.2 p.1 * derivative v U x p ∂ν) := by
  classical
  have hP (r c : α) (i j : ι) : Integrable (fun x =>
      a r c i j x * derivative v U x (j,c) * derivative v U x (i,r)) ν :=
    (((ha r c i j).continuous.mul (derivative_smooth v U hU (j,c)).continuous).mul
      (derivative_smooth v U hU (i,r)).continuous).integrable_of_hasCompactSupport
      (derivative_compact v U hcU (i,r)).mul_left
  have hQ (r c : α) (i : ι) : Integrable (fun x =>
      B r c i x * U x c * derivative v U x (i,r)) ν :=
    (((hB r c i).continuous.mul (hU c).continuous).mul
      (derivative_smooth v U hU (i,r)).continuous).integrable_of_hasCompactSupport
      (derivative_compact v U hcU (i,r)).mul_left
  have hZ (r c : α) : Integrable (fun x => C r c x * U x c * U x r) ν :=
    (((hC r c).mul (hU c).continuous).mul (hU r).continuous).integrable_of_hasCompactSupport
      (hcU r).mul_left
  have hF (r : α) : Integrable (fun x => f x r * U x r) ν :=
    ((hf r).mul (hU r).continuous).integrable_of_hasCompactSupport (hcU r).mul_left
  have hG (p : ι × α) : Integrable (fun x => g x p.2 p.1 * derivative v U x p) ν :=
    ((hg p.2 p.1).continuous.mul (derivative_smooth v U hU p).continuous).integrable_of_hasCompactSupport
      (derivative_compact v U hcU p).mul_left
  have hr (r : α) := (row_identity ν v a B C U ha hB hC hU hcU r).symm.trans
    (forcing_row ν v a B C U f g hU hcU hf hg heq r)
  have hs := congrArg (fun t : α → ℝ => ∑ r, t r) (funext hr)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  have hsumP (r c : α) := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hP r c i j))
  have hsumP' (r : α) := integrable_finsetSum Finset.univ (fun c _ => hsumP r c)
  simp only [principal]
  rw [integral_finsetSum _ (fun r _ => hsumP' r)]
  simp_rw [integral_finsetSum _ (fun c _ => hsumP _ c),
    integral_finsetSum _ (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hP _ _ i j)),
    integral_finsetSum _ (fun j _ => hP _ _ _ j)]
  rw [integral_finsetSum _ (fun r _ => hF r)]
  have hflux (p : ι × α) : Integrable (fun x => flux B U x p * derivative v U x p) ν := by
    simp only [flux, Finset.sum_mul]
    exact integrable_finsetSum _ (fun c _ => hQ p.2 c p.1)
  rw [integral_finsetSum _ (fun p _ => hflux p)]
  simp only [flux, Finset.sum_mul]
  simp_rw [integral_finsetSum _ (fun c _ => hQ _ c _)]
  simp only [zeroth]
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum Finset.univ (fun c _ => hZ r c))]
  simp_rw [integral_finsetSum _ (fun c _ => hZ _ c)]
  rw [integral_finsetSum _ (fun p _ => hG p)]
  have hswapQ : (∑ p : ι × α, ∑ c, ∫ x,
      B p.2 c p.1 x * U x c * derivative v U x p ∂ν) =
      ∑ r, ∑ c, ∑ i, ∫ x, B r c i x * U x c * derivative v U x (i,r) ∂ν := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
  have hswapG : (∑ p : ι × α, ∫ x, g x p.2 p.1 * derivative v U x p ∂ν) =
      ∑ r, ∑ i, ∫ x, g x r i * derivative v U x (i,r) ∂ν := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hswapQ, hswapG]
  linarith

/-- A fixed coefficient-dependent buffer constant, valid also in dimension zero. -/
def bufferConstant (α ι : Type*) [Fintype α] [Fintype ι] (ell b c : ℝ) : ℝ :=
  1/2 + (Fintype.card α : ℝ)*c +
    (Fintype.card (ι × α) : ℝ)*(Fintype.card α : ℝ)*b^2/ell

theorem zeroth_le (C : α → α → E → ℝ) (U : E → α → ℝ)
    (x : E) (c : ℝ) (hc : 0 ≤ c) (hC : ∀ r s, |C r s x| ≤ c) :
    -zeroth C U x ≤ (Fintype.card α : ℝ)*c*valueSq U x := by
  classical
  have hh (r s : α) : -(C r s x * U x s * U x r) ≤
      (c/2)*((U x s)^2+(U x r)^2) := by
    have hm : |U x s * U x r| ≤ ((U x s)^2+(U x r)^2)/2 := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (U x s + U x r), sq_nonneg (U x s - U x r)]
    calc
      _ ≤ |C r s x * U x s * U x r| := neg_le_abs _
      _ = |C r s x| * |U x s * U x r| := by simp only [abs_mul]; ring
      _ ≤ c * |U x s * U x r| := mul_le_mul_of_nonneg_right (hC r s) (abs_nonneg _)
      _ ≤ c * (((U x s)^2+(U x r)^2)/2) := mul_le_mul_of_nonneg_left hm hc
      _ = _ := by ring
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hh r s))
  simp only [zeroth, Finset.sum_neg_distrib] at *
  refine hs.trans_eq ?_
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  simp only [valueSq]
  ring

/-- Pointwise Young estimate for the finite lower-order and forcing terms. -/
theorem young_system (v : ι → E) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U f : E → α → ℝ) (g : E → α → ι → ℝ)
    (x : E) (ell b c : ℝ) (hell : 0 < ell) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hB : ∀ r s i, |B r s i x| ≤ b) (hC : ∀ r s, |C r s x| ≤ c) :
    (∑ r, f x r * U x r) + (∑ p, flux B U x p * derivative v U x p) -
      zeroth C U x - (∑ p, g x p.2 p.1 * derivative v U x p) ≤
      (ell/2)*gradientSq v U x + (1/2)*valueSq f x +
      bufferConstant α ι ell b c*valueSq U x +
      (1/ell)*∑ p : ι × α, (g x p.2 p.1)^2 := by
  classical
  have hfu : (∑ r, f x r * U x r) ≤ (1/2)*valueSq f x + (1/2)*valueSq U x := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
      show f x r * U x r ≤ (1/2)*(f x r)^2+(1/2)*(U x r)^2 by
        nlinarith [sq_nonneg (f x r-U x r)])
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, valueSq] using h
  have hfg : (∑ p, flux B U x p * derivative v U x p) -
      (∑ p, g x p.2 p.1 * derivative v U x p) ≤
      (ell/2)*gradientSq v U x +
      (1/ell)*((Fintype.card (ι × α) : ℝ)*(Fintype.card α : ℝ)*b^2*valueSq U x +
        ∑ p : ι × α, (g x p.2 p.1)^2) := by
    have hp (p : ι × α) : flux B U x p * derivative v U x p -
        g x p.2 p.1 * derivative v U x p ≤
        (ell/2)*(derivative v U x p)^2 +
        (1/ell)*((Fintype.card α : ℝ)*b^2*valueSq U x + (g x p.2 p.1)^2) :=
      (young_two ell hell (flux B U x p) (g x p.2 p.1) (derivative v U x p)).trans
        (by gcongr; exact flux_sq_le B U x b hb hB p)
    have h := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hp p)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    dsimp only [gradientSq]
    convert h using 1; ring
  have hz := zeroth_le C U x c hc hC
  dsimp only [bufferConstant]
  convert add_le_add (add_le_add hfu hfg) hz using 1 <;> ring

theorem derivative_memLp (v : ι → E) (U : E → α → ℝ)
    (hU : ∀ c, ContDiff ℝ ∞ (fun x => U x c))
    (hcU : ∀ c, HasCompactSupport (fun x => U x c)) (p : ι × α) :
    MemLp (fun x => derivative v U x p) 2 ν :=
  (derivative_smooth v U hU p).continuous.memLp_of_hasCompactSupport
    (derivative_compact v U hcU p)

/-- Coercive energy estimate using ellipticity and coefficient bounds only on the buffer.
No derivative of an unsmoothed limit appears in the statement. -/
theorem energy_estimate (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U f : E → α → ℝ) (g : E → α → ι → ℝ)
    (K : Set E) (hK : IsCompact K)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hC : ∀ r c, Continuous (C r c))
    (hU : ∀ c, ContDiff ℝ ∞ (fun x => U x c))
    (hUK : ∀ c, tsupport (fun x => U x c) ⊆ K)
    (hf : ∀ r, Continuous (fun x => f x r))
    (hg : ∀ r i, ContDiff ℝ ∞ (fun x => g x r i))
    (hf2 : ∀ r, MemLp (fun x => f x r) 2 ν)
    (hg2 : ∀ r i, MemLp (fun x => g x r i) 2 ν)
    (ell b c : ℝ) (hell : 0 < ell) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hboundB : ∀ x ∈ K, ∀ r s i, |B r s i x| ≤ b)
    (hboundC : ∀ x ∈ K, ∀ r s, |C r s x| ≤ c)
    (hcoercive : ∀ x ∈ K, ∀ ξ : (ι × α) → ℝ,
      ell * ∑ p, (ξ p)^2 ≤ ∑ r, ∑ s, ∑ i, ∑ j,
        a r s i j x * ξ (j,s) * ξ (i,r))
    (heq : ∀ x r, divergenceSystemApply v a B C U x r =
      f x r + ∑ i, fderiv ℝ (fun y => g y r i) x (v i)) :
    (ell/2)*(∫ x, gradientSq v U x ∂ν) ≤
      (1/2)*(∫ x, valueSq f x ∂ν) +
      bufferConstant α ι ell b c*(∫ x, valueSq U x ∂ν) +
      (1/ell)*(∫ x, ∑ p : ι × α, (g x p.2 p.1)^2 ∂ν) := by
  classical
  have hcU (r : α) : HasCompactSupport (fun x => U x r) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hUK r)
  have hd := derivative_smooth v U hU
  have hcd := derivative_compact v U hcU
  have hiD : Integrable (gradientSq v U) ν :=
    integrable_finsetSum _ (fun p _ => (derivative_memLp ν v U hU hcU p).integrable_sq)
  have hiU : Integrable (valueSq U) ν :=
    integrable_finsetSum _ (fun r _ =>
      ((hU r).continuous.memLp_of_hasCompactSupport (hcU r) (p := 2) (μ := ν)).integrable_sq)
  have hif : Integrable (valueSq f) ν := integrable_finsetSum _ (fun r _ => (hf2 r).integrable_sq)
  have hig : Integrable (fun x => ∑ p : ι × α, (g x p.2 p.1)^2) ν :=
    integrable_finsetSum _ (fun p _ => (hg2 p.2 p.1).integrable_sq)
  have hiP : Integrable (principal v a U) ν := by
    apply integrable_finsetSum _ (fun r _ => ?_)
    apply integrable_finsetSum _ (fun s _ => ?_)
    apply integrable_finsetSum _ (fun i _ => ?_)
    apply integrable_finsetSum _ (fun j _ => ?_)
    exact (((ha r s i j).continuous.mul (hd (j,s)).continuous).mul
      (hd (i,r)).continuous).integrable_of_hasCompactSupport (hcd (i,r)).mul_left
  have hiF : Integrable (fun x => ∑ r, f x r * U x r) ν :=
    integrable_finsetSum _ (fun r _ =>
      ((hf r).mul (hU r).continuous).integrable_of_hasCompactSupport (hcU r).mul_left)
  have hiQ : Integrable (fun x => ∑ p, flux B U x p * derivative v U x p) ν := by
    apply integrable_finsetSum _ (fun p _ => ?_)
    simp only [flux, Finset.sum_mul]
    apply integrable_finsetSum _ (fun s _ => ?_)
    exact (((hB p.2 s p.1).continuous.mul (hU s).continuous).mul (hd p).continuous
      ).integrable_of_hasCompactSupport (hcd p).mul_left
  have hiZ : Integrable (zeroth C U) ν := by
    apply integrable_finsetSum _ (fun r _ => ?_)
    apply integrable_finsetSum _ (fun s _ => ?_)
    exact (((hC r s).mul (hU s).continuous).mul (hU r).continuous
      ).integrable_of_hasCompactSupport (hcU r).mul_left
  have hiG : Integrable (fun x => ∑ p, g x p.2 p.1 * derivative v U x p) ν :=
    integrable_finsetSum _ (fun p _ =>
      ((hg p.2 p.1).continuous.mul (hd p).continuous
        ).integrable_of_hasCompactSupport (hcd p).mul_left)
  have hzero (x : E) (hx : x ∉ K) :
      (∀ r, U x r = 0) ∧ (∀ p, derivative v U x p = 0) := by
    constructor
    · intro r
      by_contra h
      exact hx (hUK r (subset_tsupport _ h))
    · intro p
      by_contra h
      exact hx (hUK p.2 (tsupport_fderiv_apply_subset ℝ (v p.1) (subset_tsupport _ h)))
  have hcoer (x : E) : ell * gradientSq v U x ≤ principal v a U x := by
    by_cases hx : x ∈ K
    · exact hcoercive x hx (derivative v U x)
    · obtain ⟨_, hz⟩ := hzero x hx
      simp only [gradientSq, principal, hz, zero_pow two_ne_zero, mul_zero,
        Finset.sum_const_zero, le_refl]
  have hyoung (x : E) :
      (∑ r, f x r * U x r) + (∑ p, flux B U x p * derivative v U x p) -
        zeroth C U x - (∑ p, g x p.2 p.1 * derivative v U x p) ≤
        (ell/2)*gradientSq v U x + (1/2)*valueSq f x +
        bufferConstant α ι ell b c*valueSq U x +
        (1/ell)*∑ p : ι × α, (g x p.2 p.1)^2 := by
    by_cases hx : x ∈ K
    · exact young_system v B C U f g x ell b c hell hb hc (hboundB x hx) (hboundC x hx)
    · obtain ⟨hzU, hzD⟩ := hzero x hx
      simp only [gradientSq, valueSq, zeroth, hzU, hzD, zero_pow two_ne_zero,
        mul_zero, Finset.sum_const_zero, zero_add, add_zero, sub_zero]
      positivity
  have hci := integral_mono (hiD.const_mul ell) hiP hcoer
  rw [integral_const_mul] at hci
  have hyi := integral_mono (((hiF.add hiQ).sub hiZ).sub hiG)
    ((((hiD.const_mul (ell/2)).add (hif.const_mul (1/2))).add
      (hiU.const_mul (bufferConstant α ι ell b c))).add (hig.const_mul (1/ell))) hyoung
  simp only [Pi.add_apply, Pi.sub_apply] at hyi
  rw [integral_sub (f := fun x => (∑ r, f x r * U x r) +
      (∑ p, flux B U x p * derivative v U x p) - zeroth C U x)
      (g := fun x => ∑ p, g x p.2 p.1 * derivative v U x p)
      ((hiF.add hiQ).sub hiZ) hiG,
    integral_sub (f := fun x => (∑ r, f x r * U x r) +
      (∑ p, flux B U x p * derivative v U x p)) (g := zeroth C U) (hiF.add hiQ) hiZ,
    integral_add hiF hiQ,
    ← energy_identity ν v a B C U f g ha hB hC hU hcU hf hg heq] at hyi
  rw [integral_add (f := fun x => (ell/2)*gradientSq v U x + (1/2)*valueSq f x +
      bufferConstant α ι ell b c*valueSq U x)
      (g := fun x => (1/ell)*∑ p : ι × α, (g x p.2 p.1)^2)
      (((hiD.const_mul (ell/2)).add (hif.const_mul (1/2))).add
        (hiU.const_mul (bufferConstant α ι ell b c))) (hig.const_mul (1/ell)),
    integral_add (f := fun x => (ell/2)*gradientSq v U x + (1/2)*valueSq f x)
      (g := fun x => bufferConstant α ι ell b c*valueSq U x)
      ((hiD.const_mul (ell/2)).add (hif.const_mul (1/2)))
      (hiU.const_mul (bufferConstant α ι ell b c)),
    integral_add (f := fun x => (ell/2)*gradientSq v U x)
      (g := fun x => (1/2)*valueSq f x)
      (hiD.const_mul (ell/2)) (hif.const_mul (1/2))] at hyi
  simp only [integral_const_mul] at hyi
  linarith

theorem derivative_sub (v : ι → E) (U V : E → α → ℝ)
    (hU : ∀ c, Differentiable ℝ (fun x => U x c))
    (hV : ∀ c, Differentiable ℝ (fun x => V x c)) (x : E) (p : ι × α) :
    derivative v (fun x c => U x c - V x c) x p =
      derivative v U x p - derivative v V x p := by
  simp only [derivative]
  rw [fderiv_fun_sub (hU p.2 x) (hV p.2 x)]
  rfl

/-- Linearity of the actual smooth divergence expression, including its differentiated fluxes. -/
theorem apply_sub (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U V : E → α → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hU : ∀ c, ContDiff ℝ ∞ (fun x => U x c))
    (hV : ∀ c, ContDiff ℝ ∞ (fun x => V x c)) (x : E) (r : α) :
    divergenceSystemApply v a B C (fun x c => U x c - V x c) x r =
      divergenceSystemApply v a B C U x r - divergenceSystemApply v a B C V x r := by
  classical
  have hd (y : E) (c : α) (j : ι) := derivative_sub v U V
    (fun c => (hU c).differentiable (by simp))
    (fun c => (hV c).differentiable (by simp)) y (j,c)
  have hAsub (c : α) (i j : ι) :
      (fun z => a r c i j z * fderiv ℝ (fun y => U y c - V y c) z (v j)) =
      (fun z => a r c i j z * derivative v U z (j,c)) -
        (fun z => a r c i j z * derivative v V z (j,c)) := by
    funext z
    change a r c i j z * derivative v (fun x c => U x c - V x c) z (j,c) = _
    rw [hd]
    dsimp only [Pi.sub_apply]
    ring
  have hBsub (c : α) (i : ι) :
      (fun z => B r c i z * (U z c - V z c)) =
      (fun z => B r c i z * U z c) - (fun z => B r c i z * V z c) := by
    funext z
    dsimp only [Pi.sub_apply]
    ring
  simp only [divergenceSystemApply]
  simp_rw [hAsub, hBsub]
  simp_rw [fderiv_sub (((ha r _ _ _).mul (derivative_smooth v U hU _)).differentiable (by simp) x)
      (((ha r _ _ _).mul (derivative_smooth v V hV _)).differentiable (by simp) x),
    fderiv_sub (((hB r _ _).mul (hU _)).differentiable (by simp) x)
      (((hB r _ _).mul (hV _)).differentiable (by simp) x)]
  simp only [sub_apply, Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [derivative]
  ring

/-- Subtracting two honest residual equations gives the residual of their difference. -/
theorem residual_sub (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U V f h : E → α → ℝ)
    (g k : E → α → ι → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hU : ∀ c, ContDiff ℝ ∞ (fun x => U x c))
    (hV : ∀ c, ContDiff ℝ ∞ (fun x => V x c))
    (hg : ∀ r i, Differentiable ℝ (fun x => g x r i))
    (hk : ∀ r i, Differentiable ℝ (fun x => k x r i))
    (heqU : ∀ x r, divergenceSystemApply v a B C U x r =
      f x r + ∑ i, fderiv ℝ (fun y => g y r i) x (v i))
    (heqV : ∀ x r, divergenceSystemApply v a B C V x r =
      h x r + ∑ i, fderiv ℝ (fun y => k y r i) x (v i)) (x : E) (r : α) :
    divergenceSystemApply v a B C (fun x c => U x c - V x c) x r =
      (f x r - h x r) + ∑ i, fderiv ℝ (fun y => g y r i - k y r i) x (v i) := by
  rw [apply_sub v a B C U V ha hB hU hV, heqU, heqV]
  simp_rw [fderiv_fun_sub (hg r _ x) (hk r _ x)]
  simp only [sub_apply, Finset.sum_sub_distrib]
  ring

/-- Actual scalar L² norm-square equals the squared integral of the representative. -/
theorem toLp_norm_sq (f : E → ℝ) (hf : MemLp f 2 ν) :
    ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Strong scalar L² convergence gives the exact double-index squared-integral Cauchy limit. -/
theorem pair_sq_tendsto_zero (f : ℕ → E → ℝ) (f0 : E → ℝ)
    (hf : ∀ m, MemLp (f m) 2 ν) (hf0 : MemLp f0 2 ν)
    (ht : Tendsto (fun m => ∫ x, ‖f m x-f0 x‖^2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫ x, (f p.1 x-f p.2 x)^2 ∂ν) atTop (𝓝 0) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hts : Tendsto (fun m => ∫ x, (f m x-f0 x)^2 ∂ν) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs, sq_abs] using ht
  have hb (p : ℕ × ℕ) : (∫ x, (f p.1 x-f p.2 x)^2 ∂ν) ≤
      2*(∫ x, (f p.1 x-f0 x)^2 ∂ν)+2*(∫ x, (f p.2 x-f0 x)^2 ∂ν) := by
    have hm := ((hf p.1).sub hf0).integrable_sq
    have hn := ((hf p.2).sub hf0).integrable_sq
    calc
      _ ≤ ∫ x, 2*(f p.1 x-f0 x)^2+2*(f p.2 x-f0 x)^2 ∂ν :=
        integral_mono ((hf p.1).sub (hf p.2)).integrable_sq
          ((hm.const_mul 2).add (hn.const_mul 2))
          (fun x => by
            change (f p.1 x-f p.2 x)^2 ≤ _
            nlinarith [sq_nonneg (f p.1 x+f p.2 x-2*f0 x)])
      _ = _ := by
        rw [integral_add (f := fun x => 2*(f p.1 x-f0 x)^2)
          (g := fun x => 2*(f p.2 x-f0 x)^2) (hm.const_mul 2) (hn.const_mul 2),
          integral_const_mul, integral_const_mul]
  exact squeeze_zero (fun p => integral_nonneg fun x => sq_nonneg _) hb
    (by simpa only [mul_zero, add_zero, Function.comp_def] using
      ((hts.comp hfst).const_mul 2).add ((hts.comp hsnd).const_mul 2))

/-- Finite strong L² convergence controls the sum of all double-index errors. -/
theorem pair_valueSq_tendsto_zero {κ : Type*} [Fintype κ]
    (f : ℕ → E → κ → ℝ) (f0 : E → κ → ℝ)
    (hf : ∀ m r, MemLp (fun x => f m x r) 2 ν)
    (hf0 : ∀ r, MemLp (fun x => f0 x r) 2 ν)
    (ht : ∀ r, Tendsto (fun m => ∫ x, ‖f m x r-f0 x r‖^2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫ x, valueSq (fun x r => f p.1 x r-f p.2 x r) x ∂ν)
      atTop (𝓝 0) := by
  classical
  have hh := tendsto_finsetSum Finset.univ (fun r _ =>
    pair_sq_tendsto_zero ν (fun m x => f m x r) (fun x => f0 x r)
      (fun m => hf m r) (hf0 r) (ht r))
  simp only [Finset.sum_const_zero] at hh
  convert hh using 1
  funext p
  exact integral_finsetSum _ (fun r _ => ((hf p.1 r).sub (hf p.2 r)).integrable_sq)

/-- The integral criterion gives Cauchy convergence in the genuine scalar Lp space. -/
theorem cauchySeq_toLp_of_pair_sq (f : ℕ → E → ℝ)
    (hf : ∀ m, MemLp (f m) 2 ν)
    (ht : Tendsto (fun p : ℕ × ℕ => ∫ x, (f p.1 x-f p.2 x)^2 ∂ν) atTop (𝓝 0)) :
    CauchySeq (fun m => (hf m).toLp (f m)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have he := ht.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.mp he
  refine ⟨N, fun m hm n hn => ?_⟩
  have hsq : dist ((hf m).toLp (f m)) ((hf n).toLp (f n))^2 =
      ∫ x, (f m x-f n x)^2 ∂ν := by
    rw [dist_eq_norm, ← MemLp.toLp_sub]
    exact toLp_norm_sq ν _ ((hf m).sub (hf n))
  have h := hN m hm n hn
  rw [← hsq] at h
  nlinarith

/-- The energy estimate turns L² Cauchy values and residuals into L² Cauchy gradients.
The hypotheses refer only to smooth fields and their actual pointwise residuals. -/
theorem gradient_pair_sq_tendsto_zero (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U f : ℕ → E → α → ℝ)
    (g : ℕ → E → α → ι → ℝ) (K : Set E) (hK : IsCompact K)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hC : ∀ r c, Continuous (C r c))
    (hU : ∀ m c, ContDiff ℝ ∞ (fun x => U m x c))
    (hUK : ∀ m c, tsupport (fun x => U m x c) ⊆ K)
    (hf : ∀ m r, Continuous (fun x => f m x r))
    (hg : ∀ m r i, ContDiff ℝ ∞ (fun x => g m x r i))
    (hf2 : ∀ m r, MemLp (fun x => f m x r) 2 ν)
    (hg2 : ∀ m r i, MemLp (fun x => g m x r i) 2 ν)
    (ell b c : ℝ) (hell : 0 < ell) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hboundB : ∀ x ∈ K, ∀ r s i, |B r s i x| ≤ b)
    (hboundC : ∀ x ∈ K, ∀ r s, |C r s x| ≤ c)
    (hcoercive : ∀ x ∈ K, ∀ ξ : (ι × α) → ℝ,
      ell * ∑ p, (ξ p)^2 ≤ ∑ r, ∑ s, ∑ i, ∑ j,
        a r s i j x * ξ (j,s) * ξ (i,r))
    (heq : ∀ m x r, divergenceSystemApply v a B C (U m) x r =
      f m x r + ∑ i, fderiv ℝ (fun y => g m y r i) x (v i))
    (hUt : Tendsto (fun p : ℕ × ℕ =>
      ∫ x, valueSq (fun x r => U p.1 x r-U p.2 x r) x ∂ν) atTop (𝓝 0))
    (hft : Tendsto (fun p : ℕ × ℕ =>
      ∫ x, valueSq (fun x r => f p.1 x r-f p.2 x r) x ∂ν) atTop (𝓝 0))
    (hgt : Tendsto (fun p : ℕ × ℕ =>
      ∫ x, ∑ q : ι × α, (g p.1 x q.2 q.1-g p.2 x q.2 q.1)^2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ =>
      ∫ x, gradientSq v (fun x r => U p.1 x r-U p.2 x r) x ∂ν) atTop (𝓝 0) := by
  classical
  let R (p : ℕ × ℕ) : ℝ :=
    (1/2)*(∫ x, valueSq (fun x r => f p.1 x r-f p.2 x r) x ∂ν) +
    bufferConstant α ι ell b c*(∫ x, valueSq (fun x r => U p.1 x r-U p.2 x r) x ∂ν) +
    (1/ell)*(∫ x, ∑ q : ι × α, (g p.1 x q.2 q.1-g p.2 x q.2 q.1)^2 ∂ν)
  have htR : Tendsto R atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((hft.const_mul (1/2)).add (hUt.const_mul (bufferConstant α ι ell b c))).add
        (hgt.const_mul (1/ell))
  have hbnd (p : ℕ × ℕ) :
      (∫ x, gradientSq v (fun x r => U p.1 x r-U p.2 x r) x ∂ν) ≤ R p/(ell/2) := by
    apply (le_div_iff₀ (half_pos hell)).mpr
    have hsubK (r : α) : tsupport (fun x => U p.1 x r-U p.2 x r) ⊆ K :=
      (tsupport_sub _ _).trans (Set.union_subset (hUK p.1 r) (hUK p.2 r))
    have h := energy_estimate ν v a B C
      (fun x r => U p.1 x r-U p.2 x r)
      (fun x r => f p.1 x r-f p.2 x r)
      (fun x r i => g p.1 x r i-g p.2 x r i) K hK ha hB hC
      (fun r => (hU p.1 r).sub (hU p.2 r)) hsubK
      (fun r => (hf p.1 r).sub (hf p.2 r))
      (fun r i => (hg p.1 r i).sub (hg p.2 r i))
      (fun r => (hf2 p.1 r).sub (hf2 p.2 r))
      (fun r i => (hg2 p.1 r i).sub (hg2 p.2 r i))
      ell b c hell hb hc hboundB hboundC hcoercive
      (residual_sub v a B C (U p.1) (U p.2) (f p.1) (f p.2) (g p.1) (g p.2)
        ha hB (hU p.1) (hU p.2)
        (fun r i => (hg p.1 r i).differentiable (by simp))
        (fun r i => (hg p.2 r i).differentiable (by simp)) (heq p.1) (heq p.2))
    dsimp only [R]
    linarith
  exact squeeze_zero (fun p => integral_nonneg fun x =>
      Finset.sum_nonneg fun q _ => sq_nonneg _) hbnd
    (by simpa only [zero_div] using htR.div_const (ell/2))

/-- Total gradient squared-integral Cauchy control implies componentwise actual Lp Cauchy control. -/
theorem gradient_cauchySeq_toLp (v : ι → E) (U : ℕ → E → α → ℝ)
    (hU : ∀ m c, ContDiff ℝ ∞ (fun x => U m x c))
    (hcU : ∀ m c, HasCompactSupport (fun x => U m x c))
    (ht : Tendsto (fun p : ℕ × ℕ =>
      ∫ x, gradientSq v (fun x r => U p.1 x r-U p.2 x r) x ∂ν) atTop (𝓝 0)) :
    ∀ q : ι × α, CauchySeq (fun m =>
      (derivative_memLp ν v (U m) (hU m) (hcU m) q).toLp
        (fun x => derivative v (U m) x q)) := by
  classical
  intro q
  apply cauchySeq_toLp_of_pair_sq ν _
    (fun m => derivative_memLp ν v (U m) (hU m) (hcU m) q)
  have hdb (p : ℕ × ℕ) :
      (∫ x, (derivative v (U p.1) x q-derivative v (U p.2) x q)^2 ∂ν) ≤
      ∫ x, gradientSq v (fun x r => U p.1 x r-U p.2 x r) x ∂ν := by
    have hsub (x : E) (s : ι × α) := derivative_sub v (U p.1) (U p.2)
      (fun r => (hU p.1 r).differentiable (by simp))
      (fun r => (hU p.2 r).differentiable (by simp)) x s
    have hiq := ((derivative_memLp ν v (U p.1) (hU p.1) (hcU p.1) q).sub
      (derivative_memLp ν v (U p.2) (hU p.2) (hcU p.2) q)).integrable_sq
    have hiD : Integrable (gradientSq v (fun x r => U p.1 x r-U p.2 x r)) ν :=
      integrable_finsetSum _ (fun s _ =>
        (derivative_memLp ν v _ (fun r => (hU p.1 r).sub (hU p.2 r))
          (fun r => (hcU p.1 r).sub (hcU p.2 r)) s).integrable_sq)
    apply integral_mono hiq hiD
    intro x
    change (derivative v (U p.1) x q-derivative v (U p.2) x q)^2 ≤ _
    rw [← hsub x q]
    exact Finset.single_le_sum (fun s _ => sq_nonneg _) (Finset.mem_univ q)
  exact squeeze_zero (fun p => integral_nonneg fun x => sq_nonneg _) hdb ht

/-- Smooth compact solutions whose values and actual divergence residuals converge strongly
in L² have Cauchy directional derivatives in the genuine scalar Lp spaces. The raw value
limit is only assumed to be L²; no weak derivative or H¹ membership is assumed. -/
theorem gradient_cauchySeq_of_strong_L2 (v : ι → E)
    (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (C : α → α → E → ℝ) (U f : ℕ → E → α → ℝ)
    (g : ℕ → E → α → ι → ℝ) (u0 f0 : E → α → ℝ) (g0 : E → α → ι → ℝ)
    (K : Set E) (hK : IsCompact K)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    (hC : ∀ r c, Continuous (C r c))
    (hU : ∀ m c, ContDiff ℝ ∞ (fun x => U m x c))
    (hUK : ∀ m c, tsupport (fun x => U m x c) ⊆ K)
    (hf : ∀ m r, Continuous (fun x => f m x r))
    (hg : ∀ m r i, ContDiff ℝ ∞ (fun x => g m x r i))
    (hf2 : ∀ m r, MemLp (fun x => f m x r) 2 ν)
    (hg2 : ∀ m r i, MemLp (fun x => g m x r i) 2 ν)
    (hu02 : ∀ r, MemLp (fun x => u0 x r) 2 ν)
    (hf02 : ∀ r, MemLp (fun x => f0 x r) 2 ν)
    (hg02 : ∀ r i, MemLp (fun x => g0 x r i) 2 ν)
    (ell b c : ℝ) (hell : 0 < ell) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hboundB : ∀ x ∈ K, ∀ r s i, |B r s i x| ≤ b)
    (hboundC : ∀ x ∈ K, ∀ r s, |C r s x| ≤ c)
    (hcoercive : ∀ x ∈ K, ∀ ξ : (ι × α) → ℝ,
      ell * ∑ p, (ξ p)^2 ≤ ∑ r, ∑ s, ∑ i, ∑ j,
        a r s i j x * ξ (j,s) * ξ (i,r))
    (heq : ∀ m x r, divergenceSystemApply v a B C (U m) x r =
      f m x r + ∑ i, fderiv ℝ (fun y => g m y r i) x (v i))
    (hUt : ∀ r, Tendsto (fun m => ∫ x, ‖U m x r-u0 x r‖^2 ∂ν) atTop (𝓝 0))
    (hft : ∀ r, Tendsto (fun m => ∫ x, ‖f m x r-f0 x r‖^2 ∂ν) atTop (𝓝 0))
    (hgt : ∀ r i, Tendsto (fun m => ∫ x, ‖g m x r i-g0 x r i‖^2 ∂ν) atTop (𝓝 0)) :
    ∀ q : ι × α, CauchySeq (fun m =>
      (derivative_memLp ν v (U m) (hU m)
        (fun r => hK.of_isClosed_subset (isClosed_tsupport _) (hUK m r)) q).toLp
        (fun x => derivative v (U m) x q)) := by
  have hcU (m : ℕ) (r : α) : HasCompactSupport (fun x => U m x r) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hUK m r)
  have hU2 (m : ℕ) (r : α) : MemLp (fun x => U m x r) 2 ν :=
    (hU m r).continuous.memLp_of_hasCompactSupport (hcU m r)
  apply gradient_cauchySeq_toLp ν v U hU hcU
  apply gradient_pair_sq_tendsto_zero ν v a B C U f g K hK ha hB hC hU hUK hf hg
    hf2 hg2 ell b c hell hb hc hboundB hboundC hcoercive heq
  · exact pair_valueSq_tendsto_zero ν U u0 hU2 hu02 hUt
  · exact pair_valueSq_tendsto_zero ν f f0 hf2 hf02 hft
  · exact pair_valueSq_tendsto_zero ν (fun m x (q : ι × α) => g m x q.2 q.1)
      (fun x (q : ι × α) => g0 x q.2 q.1)
      (fun m q => hg2 m q.2 q.1) (fun q => hg02 q.2 q.1) (fun q => hgt q.2 q.1)

end DivergenceEnergy
end Yau.LeafProofs.L03
