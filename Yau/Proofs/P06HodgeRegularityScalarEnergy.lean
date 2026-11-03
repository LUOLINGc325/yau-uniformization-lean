import Yau.Proofs.P06HodgeRegularityEnergy

/-! Differentiating a smooth scalar-principal divergence equation. The
source derivative is kept as divergence flux, so its L² norm suffices. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- True directional derivative in a fixed real coordinate direction. -/
def regularityDirection (e : E) (u : E → ℝ) : E → ℝ := fun z => fderiv ℝ u z e

theorem regularityDirection_contDiff {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (e : E) :
    ContDiff ℝ ∞ (regularityDirection e u) :=
  (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem regularityDirection_mul {u w : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (e : E) :
    regularityDirection e (fun z => u z * w z) =
      fun z => regularityDirection e u z * w z + u z * regularityDirection e w z := by
  funext z
  rw [regularityDirection, fderiv_fun_mul (hu.differentiable (by simp) z) (hw.differentiable (by simp) z)]
  simp only [add_apply, smul_apply, smul_eq_mul, regularityDirection]
  ring

theorem regularityDirection_add {u w : E → ℝ}
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w) (e : E) :
    regularityDirection e (fun z => u z + w z) =
      fun z => regularityDirection e u z + regularityDirection e w z := by
  funext z
  rw [regularityDirection, fderiv_fun_add (hu.differentiable (by simp) z) (hw.differentiable (by simp) z)]
  rfl

theorem regularityDirection_neg {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (e : E) :
    regularityDirection e (-u) = -regularityDirection e u := by
  funext z
  rw [regularityDirection, fderiv_neg]
  rfl

theorem regularityDirection_sum {ι : Type*} [Fintype ι]
    (f : ι → E → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (e : E) :
    regularityDirection e (fun z => ∑ i, f i z) =
      fun z => ∑ i, regularityDirection e (f i) z := by
  classical
  funext z
  rw [regularityDirection, fderiv_fun_sum (fun i _ => (hf i).differentiable (by simp) z)]
  simp only [ContinuousLinearMap.sum_apply, regularityDirection]

/-- Smooth mixed directional derivatives commute in the actual Fréchet calculus. -/
theorem regularityDirection_commute {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (e f : E) :
    regularityDirection e (regularityDirection f u) =
      regularityDirection f (regularityDirection e u) := by
  funext z
  have hs : IsSymmSndFDerivAt ℝ u z := hu.contDiffAt.isSymmSndFDerivAt (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  have heq (e f : E) : fderiv ℝ (fun y => fderiv ℝ u y f) z e =
      fderiv ℝ (fderiv ℝ u) z e f :=
    DFunLike.congr_fun ((ContinuousLinearMap.apply ℝ ℝ f).hasFDerivAt.comp z hd.hasFDerivAt).fderiv e
  exact (heq e f).trans ((hs e f).trans (heq f e).symm)

variable {ι : Type*} [Fintype ι]

/-- Actual scalar-principal divergence expression. -/
def regularityScalarDiv (v : ι → E) (q : ι → ι → E → ℝ) (u : E → ℝ) : E → ℝ :=
  fun z => -(∑ i, ∑ j, regularityDirection (v i)
    (fun y => q i j y * regularityDirection (v j) u y) z)

theorem regularityScalarDiv_contDiff (v : ι → E) (q : ι → ι → E → ℝ)
    {u : E → ℝ} (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (regularityScalarDiv v q u) := by
  exact (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    regularityDirection_contDiff ((hq i j).mul (regularityDirection_contDiff hu (v j))) (v i)).neg

/-- Differentiating introduces only a divergence flux involving Dq and Du;
the derivative of the source is itself retained in divergence form. -/
theorem regularityScalarDiv_derivative (v : ι → E) (q : ι → ι → E → ℝ)
    {u : E → ℝ} (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hu : ContDiff ℝ ∞ u) (ell : ι) :
    regularityScalarDiv v q (regularityDirection (v ell) u) =
      fun z => regularityDirection (v ell) (regularityScalarDiv v q u) z +
        ∑ i, ∑ j, regularityDirection (v i)
          (fun y => regularityDirection (v ell) (q i j) y * regularityDirection (v j) u y) z := by
  classical
  have hprod (i j : ι) : regularityDirection (v ell)
      (fun y => q i j y * regularityDirection (v j) u y) =
      fun y => regularityDirection (v ell) (q i j) y * regularityDirection (v j) u y +
        q i j y * regularityDirection (v j) (regularityDirection (v ell) u) y := by
    rw [regularityDirection_mul (hq i j) (regularityDirection_contDiff hu (v j)),
      regularityDirection_commute hu (v ell) (v j)]
  have hpair (i j : ι) : regularityDirection (v i)
      (fun y => q i j y * regularityDirection (v j) (regularityDirection (v ell) u) y) =
      fun z => regularityDirection (v ell) (regularityDirection (v i)
        (fun y => q i j y * regularityDirection (v j) u y)) z -
        regularityDirection (v i)
          (fun y => regularityDirection (v ell) (q i j) y * regularityDirection (v j) u y) z := by
    have h := congrArg (regularityDirection (v i)) (hprod i j)
    rw [regularityDirection_add
      ((regularityDirection_contDiff (hq i j) (v ell)).mul (regularityDirection_contDiff hu (v j)))
      ((hq i j).mul (regularityDirection_contDiff (regularityDirection_contDiff hu (v ell)) (v j))) (v i)] at h
    rw [regularityDirection_commute
      ((hq i j).mul (regularityDirection_contDiff hu (v j))) (v i) (v ell)] at h
    funext z
    have hz := congrFun h z
    linarith
  have hsmooth (i j : ι) : ContDiff ℝ ∞ (regularityDirection (v i)
      (fun y => q i j y * regularityDirection (v j) u y)) :=
    regularityDirection_contDiff ((hq i j).mul (regularityDirection_contDiff hu (v j))) (v i)
  have hsum : regularityDirection (v ell) (regularityScalarDiv v q u) =
      fun z => -(∑ i, ∑ j, regularityDirection (v ell) (regularityDirection (v i)
        (fun y => q i j y * regularityDirection (v j) u y)) z) := by
    change regularityDirection (v ell) (-(fun z => ∑ i, ∑ j,
      regularityDirection (v i) (fun y => q i j y * regularityDirection (v j) u y) z)) = _
    rw [regularityDirection_neg (ContDiff.sum fun i _ => ContDiff.sum fun j _ => hsmooth i j),
      regularityDirection_sum
        (fun i z => ∑ j, regularityDirection (v i)
          (fun y => q i j y * regularityDirection (v j) u y) z)
        (fun i => ContDiff.sum fun j _ => hsmooth i j) (v ell)]
    funext z
    simp only [Pi.neg_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (regularityDirection_sum _ (hsmooth i) (v ell)) z
  funext z
  change -(∑ i, ∑ j, regularityDirection (v i)
    (fun y => q i j y * regularityDirection (v j) (regularityDirection (v ell) u) y) z) = _
  simp_rw [hpair, Finset.sum_sub_distrib]
  rw [hsum]
  ring


/-- The explicit source flux for one differentiated scalar-principal equation. -/
def regularityScalarFlux [DecidableEq ι] (v : ι → E) (q : ι → ι → E → ℝ)
    (u F : E → ℝ) (ell i : ι) : E → ℝ :=
  fun z => (if i = ell then F z else 0) +
    ∑ j, regularityDirection (v ell) (q i j) z * regularityDirection (v j) u z

theorem regularityScalarDiv_compact (v : ι → E) (q : ι → ι → E → ℝ)
    {u : E → ℝ} (hcu : HasCompactSupport u) : HasCompactSupport (regularityScalarDiv v q u) := by
  classical
  have hh (i j : ι) : HasCompactSupport (regularityDirection (v i)
      (fun y => q i j y * regularityDirection (v j) u y)) :=
    ((hcu.fderiv_apply ℝ (v j)).mul_left).fderiv_apply ℝ (v i)
  have hs := HasCompactSupport.finset_sum (fun i (_ : i ∈ Finset.univ) =>
    HasCompactSupport.finset_sum (fun j (_ : j ∈ Finset.univ) => hh i j))
  have hsum : HasCompactSupport (fun z => ∑ i, ∑ j, regularityDirection (v i)
      (fun y => q i j y * regularityDirection (v j) u y) z) := by
    convert hs using 1
    funext z
    simp only [Finset.sum_apply]
  exact hsum.neg


theorem regularityScalarFlux_contDiff [DecidableEq ι]
    (v : ι → E) (q : ι → ι → E → ℝ) {u F : E → ℝ}
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hu : ContDiff ℝ ∞ u)
    (hF : ContDiff ℝ ∞ F) (ell i : ι) :
    ContDiff ℝ ∞ (regularityScalarFlux v q u F ell i) := by
  unfold regularityScalarFlux
  apply ContDiff.add
  · by_cases hi : i = ell
    · simpa only [hi, ite_true] using hF
    · simpa only [hi, ite_false] using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))
  · exact ContDiff.sum fun j _ => (regularityDirection_contDiff (hq i j) (v ell)).mul
      (regularityDirection_contDiff hu (v j))

theorem regularityScalarFlux_compact [DecidableEq ι]
    (v : ι → E) (q : ι → ι → E → ℝ) {u F : E → ℝ}
    (hcu : HasCompactSupport u) (hcF : HasCompactSupport F) (ell i : ι) :
    HasCompactSupport (regularityScalarFlux v q u F ell i) := by
  classical
  unfold regularityScalarFlux
  apply HasCompactSupport.add
  · by_cases hi : i = ell
    · simpa only [hi, ite_true] using hcF
    · simp only [hi, ite_false]
      exact HasCompactSupport.zero
  · have hh (j : ι) : HasCompactSupport (fun z =>
        regularityDirection (v ell) (q i j) z * regularityDirection (v j) u z) :=
      (hcu.fderiv_apply ℝ (v j)).mul_left
    have hs := HasCompactSupport.finset_sum (fun j (_ : j ∈ Finset.univ) => hh j)
    convert hs using 1
    funext z
    simp only [Finset.sum_apply]

theorem regularityScalarDiv_derivative_flux [DecidableEq ι]
    (v : ι → E) (q : ι → ι → E → ℝ) {u F : E → ℝ}
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hu : ContDiff ℝ ∞ u)
    (hF : regularityScalarDiv v q u = F) (ell : ι) (z : E) :
    regularityScalarDiv v q (regularityDirection (v ell) u) z =
      ∑ i, regularityDirection (v i) (regularityScalarFlux v q u F ell i) z := by
  classical
  have hFs : ContDiff ℝ ∞ F := hF ▸ regularityScalarDiv_contDiff v q hq hu
  have hDi (i : ι) : regularityDirection (v i) (regularityScalarFlux v q u F ell i) =
      fun z => (if i = ell then regularityDirection (v i) F z else 0) +
        ∑ j, regularityDirection (v i)
          (fun y => regularityDirection (v ell) (q i j) y * regularityDirection (v j) u y) z := by
    have hfirst : ContDiff ℝ ∞ (fun z => if i = ell then F z else 0) := by
      by_cases hi : i = ell
      · simpa only [hi, ite_true] using hFs
      · simpa only [hi, ite_false] using (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : ℝ)))
    unfold regularityScalarFlux
    rw [regularityDirection_add hfirst
      (ContDiff.sum fun j _ => (regularityDirection_contDiff (hq i j) (v ell)).mul
        (regularityDirection_contDiff hu (v j))) (v i),
      regularityDirection_sum _ (fun j =>
        (regularityDirection_contDiff (hq i j) (v ell)).mul (regularityDirection_contDiff hu (v j))) (v i)]
    by_cases hi : i = ell
    · simp only [hi, if_true]
    · simp only [hi, if_false, regularityDirection, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_add]
  rw [regularityScalarDiv_derivative v q hq hu ell, hF]
  simp_rw [hDi]
  simp only [Finset.sum_add_distrib]
  simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The smooth source H² energy step, in an explicit form retaining its
L² source flux. No bound on a derivative of the source is needed. -/
theorem regularityScalarDiv_derivative_energy
    (ν : Measure E) [ν.IsAddHaarMeasure] [DecidableEq ι]
    (v : ι → E) (q : ι → ι → E → ℝ) {u F : E → ℝ}
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hu : ContDiff ℝ ∞ u)
    (hF : regularityScalarDiv v q u = F)
    (K : Set E) (hK : IsCompact K) (huK : tsupport u ⊆ K)
    (lam : ℝ) (hlam : 0 < lam)
    (hcoercive : ∀ z ∈ K, ∀ ξ : ι → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, q i j z * ξ j * ξ i) (ell : ι) :
    (lam / 2) * (∫ z, ∑ i,
      (regularityDirection (v i) (regularityDirection (v ell) u) z)^2 ∂ν) ≤
      DivergenceEnergy.bufferConstant Unit ι lam 0 0 *
        (∫ z, (regularityDirection (v ell) u z)^2 ∂ν) +
      (1 / lam) * (∫ z, ∑ i, (regularityScalarFlux v q u F ell i z)^2 ∂ν) := by
  classical
  have hcu : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport _) huK
  have hFs : ContDiff ℝ ∞ F := hF ▸ regularityScalarDiv_contDiff v q hq hu
  have hcF : HasCompactSupport F := hF ▸ regularityScalarDiv_compact v q hcu
  have hflux (i : ι) : ContDiff ℝ ∞ (regularityScalarFlux v q u F ell i) :=
    regularityScalarFlux_contDiff v q hq hu hFs ell i
  have hcflux (i : ι) : HasCompactSupport (regularityScalarFlux v q u F ell i) :=
    regularityScalarFlux_compact v q hcu hcF ell i
  have hU := regularityDirection_contDiff hu (v ell)
  have hUK : tsupport (regularityDirection (v ell) u) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (v ell)).trans huK
  have heq (z : E) (_r : Unit) : divergenceSystemApply v
      (fun (_r _c : Unit) i j => q i j) (fun _ _ _ _ => 0) (fun _ _ _ => 0)
      (fun z (_ : Unit) => regularityDirection (v ell) u z) z _r =
      (0 : ℝ) + ∑ i, fderiv ℝ
        (fun y => regularityScalarFlux v q u F ell i y) z (v i) := by
    simp only [divergenceSystemApply, Fintype.sum_unique, fderiv_fun_const, Pi.zero_apply, zero_apply,
      mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
    exact regularityScalarDiv_derivative_flux v q hq hu hF ell z
  have hcoer (z : E) (hz : z ∈ K) (ξ : ι × Unit → ℝ) :
      lam * ∑ p, (ξ p)^2 ≤ ∑ r : Unit, ∑ c : Unit, ∑ i, ∑ j,
        q i j z * ξ (j,c) * ξ (i,r) := by
    simpa only [Fintype.sum_prod_type, Fintype.sum_unique] using
      hcoercive z hz (fun i => ξ (i,()))
  have henergy := DivergenceEnergy.energy_estimate ν v
    (fun (_r _c : Unit) i j => q i j) (fun _ _ _ _ => 0) (fun _ _ _ => 0)
    (fun z (_ : Unit) => regularityDirection (v ell) u z) (fun _ _ => 0)
    (fun z (_ : Unit) i => regularityScalarFlux v q u F ell i z) K hK
    (fun _ _ i j => hq i j) (fun _ _ _ => contDiff_const) (fun _ _ => continuous_const)
    (fun _ => hU) (fun _ => hUK) (fun _ => continuous_const) (fun _ i => hflux i)
    (fun _ => MemLp.zero') (fun _ i => (hflux i).continuous.memLp_of_hasCompactSupport (hcflux i))
    lam 0 0 hlam le_rfl le_rfl (by intros; simp) (by intros; simp) hcoer heq
  change (lam / 2) * (∫ z, ∑ i,
      (fderiv ℝ (fun y => fderiv ℝ u y (v ell)) z (v i))^2 ∂ν) ≤
    DivergenceEnergy.bufferConstant Unit ι lam 0 0 * (∫ z, (fderiv ℝ u z (v ell))^2 ∂ν) +
      (1 / lam) * (∫ z, ∑ i, (regularityScalarFlux v q u F ell i z)^2 ∂ν)
  simpa only [DivergenceEnergy.gradientSq, DivergenceEnergy.derivative, DivergenceEnergy.valueSq,
    Fintype.sum_prod_type, Fintype.sum_unique, zero_pow two_ne_zero, Finset.sum_const_zero,
    integral_zero, mul_zero, zero_add, regularityDirection] using henergy

end Yau.NodeProofs.P06Aux
