import Yau.LeafProofs.L22Convex

noncomputable section

open scoped Topology ContDiff
open Filter Set

namespace Yau.LeafProofs.L22Aux

/-- The converse second-derivative test, expressed using the actual total
derivatives. A negative second derivative would give a local maximum as well
as the assumed minimum, forcing the function to be locally constant. -/
theorem second_deriv_nonneg_of_localMin {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) :
    0 ≤ deriv (deriv f) x := by
  by_contra h
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge h
  have hmax : IsLocalMax f x :=
    isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hz : deriv (deriv f) x = 0 := by
    simpa only [deriv_const'] using heq.deriv.deriv_eq
  linarith

theorem second_deriv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    deriv (deriv (fun t : ℝ => f (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hpath : Continuous (fun t : ℝ => x + t • v) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 2 f (x + t • v) := by
    exact hpath.continuousAt.eventually (by simpa using hf.eventually (by norm_num))
  have heq : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 0]
      (fun t => fderiv ℝ f (x + t • v) v) := by
    filter_upwards [hnear] with t ht
    exact (ht.differentiableAt (by norm_num)).deriv_comp_add_smul
  rw [heq.deriv_eq]
  have hf' : ContDiffAt ℝ ((1 : ℕ) + 1) f (x + (0 : ℝ) • v) := by
    convert hf using 1 <;> norm_num
  have h := hf'.deriv_fderiv_add_smul (n := 1)
  change deriv (fun s : ℝ => iteratedFDeriv ℝ 1 f (x + s • v) (fun _ => v)) 0 =
    iteratedFDeriv ℝ 2 f (x + (0 : ℝ) • v) (fun _ => v) at h
  simpa only [iteratedFDeriv_one_apply, iteratedFDeriv_two_apply, zero_smul,
    add_zero] using h

/-- Nonnegativity of the actual Hessian at a local minimum. -/
theorem hessian_nonneg_of_localMin {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hmin : IsLocalMin f x) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  have hpath : Continuous (fun t : ℝ => x + t • v) := by fun_prop
  have hct : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    simpa only [ContinuousAt, zero_smul, add_zero] using
      (hpath.continuousAt (x := (0 : ℝ)))
  have hmin' : IsLocalMin (fun t : ℝ => f (x + t • v)) 0 := by
    simpa only [IsLocalMin, IsMinFilter, zero_smul, add_zero] using hct.eventually hmin
  rw [← second_deriv_line hf v]
  apply second_deriv_nonneg_of_localMin hmin'
  simpa only [ContinuousAt, Function.comp_def, zero_smul, add_zero] using
    hf.continuousAt.tendsto.comp hct

/-- The Hessian of a smooth convex function is positive semidefinite, stated
directly as a quadratic inequality on its actual second Fréchet derivative. -/
theorem hessian_nonneg_of_convex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ univ f) (x v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hgc : ConvexOn ℝ univ g := by
    simpa only [preimage_univ, Function.comp_def, AffineMap.lineMap_apply_module',
      add_sub_cancel_left, add_comm] using
      hconv.comp_affineMap (AffineMap.lineMap x (x + v))
  have hgs : ContDiff ℝ 2 g := by
    exact hf.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hmono : Monotone (deriv g) := by
    simpa only [monotoneOn_univ] using
      hgc.monotoneOn_deriv (fun t _ => hgs.differentiable (by norm_num) t)
  have h := hmono.deriv_nonneg (x := (0 : ℝ))
  rw [second_deriv_line hf.contDiffAt v] at h
  exact h

theorem fderiv_nonneg_of_monotone_pi {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : DifferentiableAt ℝ f x) (hmono : Monotone f)
    {v : ι → ℝ} (hv : 0 ≤ v) : 0 ≤ fderiv ℝ f x v := by
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hgmono : Monotone g := by
    intro a b hab
    apply hmono
    intro i
    change x i + a * v i ≤ x i + b * v i
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hab (hv i))
  have h := hgmono.deriv_nonneg (x := (0 : ℝ))
  have hderiv : deriv g 0 = fderiv ℝ f x v := by
    have hfx : DifferentiableAt ℝ f (x + (0 : ℝ) • v) := by simpa using hf
    simpa only [zero_smul, add_zero, g] using hfx.deriv_comp_add_smul
  rwa [hderiv] at h

theorem fderiv_coordinate_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : DifferentiableAt ℝ f x) (hmono : Monotone f) (i : ι) :
    0 ≤ fderiv ℝ f x (Pi.single i 1) := by
  classical
  apply fderiv_nonneg_of_monotone_pi hf hmono
  intro j
  by_cases h : j = i <;> simp [Pi.single_apply, h]

theorem fderiv_diagonal_eq_one {ι : Type*} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : DifferentiableAt ℝ f x)
    (htrans : ∀ t : ℝ, f (fun i => x i + t) = f x + t) :
    fderiv ℝ f x (fun _ => 1) = 1 := by
  have hfx : DifferentiableAt ℝ f (x + (0 : ℝ) • (fun _ : ι => (1 : ℝ))) := by
    simpa using hf
  have hderiv := hfx.deriv_comp_add_smul
  have heq : (fun t : ℝ => f (x + t • (fun _ : ι => (1 : ℝ)))) =
      (fun t => f x + t) := by
    funext t
    have hx : x + t • (fun _ : ι => (1 : ℝ)) = (fun i => x i + t) := by
      ext i
      simp
    rw [hx]
    exact htrans t
  rw [heq] at hderiv
  have hd : HasDerivAt (fun t : ℝ => f x + t) 1 0 := (hasDerivAt_id 0).const_add _
  rw [hd.deriv] at hderiv
  simpa only [zero_smul, add_zero] using hderiv.symm

theorem sum_fderiv_coordinate_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} {x : ι → ℝ}
    (hf : DifferentiableAt ℝ f x)
    (htrans : ∀ t : ℝ, f (fun i => x i + t) = f x + t) :
    ∑ i, fderiv ℝ f x (Pi.single i 1) = 1 := by
  classical
  rw [← map_sum]
  have hsum : (∑ i : ι, Pi.single i (1 : ℝ)) = (fun _ : ι => (1 : ℝ)) := by
    ext j
    simp
  rw [hsum]
  exact fderiv_diagonal_eq_one hf htrans

end Yau.LeafProofs.L22Aux
