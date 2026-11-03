import Yau.LeafProofs.L19Differential

/-! The bounded-cylinder Bernstein energy for the original scalar heat equation. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L24Aux
open L18Aux L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def bernsteinProfile (a : ℝ) : ℝ := Real.exp (a ^ 2 / 4)
def bernsteinE : ℝ := Real.exp (1 / 4)
def bernsteinBeta : ℝ := 1 / (4 * bernsteinE)
def localGradientConstant (n : ℕ) : ℝ :=
  Real.sqrt (8 * bernsteinE * (8 * (n : ℝ) + 18 + 16 * bernsteinE))
def bernsteinEnergy (g : SmoothMetric M) (v : M.Carrier → ℝ → ℝ)
    (x : M.Carrier) (t : ℝ) : ℝ :=
  bernsteinProfile (v x t) * gradNormSq g.form (fun y => v y t) x

def bernsteinAuxiliary (g : SmoothMetric M) (v : M.Carrier → ℝ → ℝ)
    (τ : ℝ) (x : M.Carrier) (s : ℝ) : ℝ := s * bernsteinEnergy g v x (τ + s)

theorem bernsteinProfile_contDiff : ContDiff ℝ ∞ bernsteinProfile :=
  ((contDiff_id.pow 2).div_const 4).exp

theorem bernsteinProfile_hasDerivAt (a : ℝ) :
    HasDerivAt bernsteinProfile (a / 2 * bernsteinProfile a) a := by
  have hh := (((hasDerivAt_id a).pow 2).div_const 4).exp
  convert hh using 1
  · rfl
  · dsimp [bernsteinProfile]
    ring

theorem bernsteinProfile_deriv : deriv bernsteinProfile =
    fun a => a / 2 * bernsteinProfile a :=
  funext (fun a => (bernsteinProfile_hasDerivAt a).deriv)

theorem bernsteinProfile_secondDeriv (a : ℝ) :
    deriv (deriv bernsteinProfile) a = (1 / 2 + a ^ 2 / 4) * bernsteinProfile a := by
  rw [bernsteinProfile_deriv]
  have hh := (((hasDerivAt_id a).div_const 2).mul (bernsteinProfile_hasDerivAt a)).deriv
  change deriv (fun a : ℝ => a / 2 * bernsteinProfile a) a = _ at hh
  rw [hh]
  dsimp
  ring

theorem bernsteinProfile_one_le (a : ℝ) : 1 ≤ bernsteinProfile a := by
  simpa only [bernsteinProfile, Real.exp_zero] using
    Real.exp_le_exp.mpr (div_nonneg (sq_nonneg a) (by norm_num : (0:ℝ) ≤ 4))

theorem bernsteinProfile_le_E {a : ℝ} (ha : a ^ 2 ≤ 1) :
    bernsteinProfile a ≤ bernsteinE := by
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ha (by norm_num))

theorem bernsteinE_pos : 0 < bernsteinE := Real.exp_pos _
theorem bernsteinBeta_pos : 0 < bernsteinBeta := one_div_pos.mpr (by
  exact mul_pos (by norm_num) bernsteinE_pos)

theorem positiveHeatSolution_div_pos (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    {A : ℝ} (hA : 0 < A) :
    LeafCandidates.PositiveHeatSolution h (fun x t => u x t / A) := by
  refine ⟨fun a => (hu.1 a).div_const A, ?_⟩
  intro x t ht
  refine ⟨div_pos (hu.2 x t ht).1 hA, ?_⟩
  rw [((positiveHeatSolution_hasDerivAt h hu x ht).div_const A).deriv]
  have hh := laplacian_const_mul h (positiveHeatSolution_slice h hu ht) A⁻¹ x
  simpa only [div_eq_mul_inv, mul_comm] using hh.symm

theorem gradNormSq_div_const (h : HermitianField M)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (A : ℝ) (x : M.Carrier) :
    gradNormSq h (fun y => u y / A) x = gradNormSq h u x / A ^ 2 := by
  have hs : SmoothFn (fun y => u y / A) := fun a => (hu a).div_const A
  have hh := scalarGradientPair_scalar_comp_self h hu (fun a : ℝ => a / A) x
    ((hasDerivAt_id (u x)).div_const A).differentiableAt
  have hd : deriv (fun a : ℝ => a / A) (u x) = 1 / A :=
    (show HasDerivAt (fun a : ℝ => a / A) (1 / A) (u x) from
      (hasDerivAt_id (u x)).div_const A).deriv
  rw [scalarGradientPair_eq_twice_gradNormSq h hs x,
    scalarGradientPair_eq_twice_gradNormSq h hu x, hd] at hh
  have hh' : (1 / A) ^ 2 * gradNormSq h u x = gradNormSq h u x / A ^ 2 := by
    simp only [div_eq_mul_inv, one_mul, inv_pow]
    ring
  nlinarith only [hh, hh']

theorem gradNormSq_nonneg (h : HermitianField M) {f : M.Carrier → ℝ}
    (hf : SmoothFn f) (x : M.Carrier) : 0 ≤ gradNormSq h f x := by
  have hh := scalarGradientPair_self_nonneg h f x
  rw [scalarGradientPair_eq_twice_gradNormSq h hf x] at hh
  linarith

theorem bernsteinEnergy_smoothSpaceTime (g : SmoothMetric M)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Set.Ioi 0)) :
    SmoothSpaceTime (bernsteinEnergy g v) (Set.Ioi 0) := by
  intro a
  exact (((hv a).pow 2).div_const 4).exp.mul ((smoothSpaceTime_gradNormSq g hv) a)

theorem bernsteinEnergy_nonneg (g : SmoothMetric M)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Set.Ioi 0))
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) : 0 ≤ bernsteinEnergy g v x t :=
  mul_nonneg (Real.exp_pos _).le (gradNormSq_nonneg g.form (smoothSpaceTime_slice hv ht) x)

theorem gradNormSq_le_bernsteinEnergy (g : SmoothMetric M)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Set.Ioi 0))
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    gradNormSq g.form (fun y => v y t) x ≤ bernsteinEnergy g v x t := by
  have hh := mul_le_mul_of_nonneg_right (bernsteinProfile_one_le (v x t))
    (gradNormSq_nonneg g.form (smoothSpaceTime_slice hv ht) x)
  simpa only [one_mul, bernsteinEnergy] using hh

theorem heat_energy_subcaloric (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {v : M.Carrier → ℝ → ℝ} (hv : LeafCandidates.PositiveHeatSolution g.form v)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    0 ≤ laplacian g.form (fun y => gradNormSq g.form (fun z => v z t) y) x -
      deriv (fun s => gradNormSq g.form (fun z => v z s) x) t := by
  rw [(gradNormSq_time_hasDerivAt g.form hv.1 x ht).deriv]
  have heq : (fun y => deriv (v y) t) = laplacian g.form (fun y => v y t) :=
    funext (fun y => (hv.2 y t ht).2)
  rw [heq]
  exact (div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)).trans
    (complexCD_inequality g hK hRic (positiveHeatSolution_slice g.form hv ht) x)

/-- Product pairing, kept local to this leaf. -/
theorem bernstein_pair_mul_left (h : HermitianField M)
    {a f : M.Carrier → ℝ} (ha : SmoothFn a) (hf : SmoothFn f)
    (k : M.Carrier → ℝ) (x : M.Carrier) :
    scalarGradientPair h (fun y => a y * f y) k x =
      a x * scalarGradientPair h f k x + f x * scalarGradientPair h a k x := by
  have hp := chartGradientPair_mul_left h x (inChart x k)
    ((contDiffAt_inChart ha x (mem_extChartAt_target x)).differentiableAt (by simp))
    ((contDiffAt_inChart hf x (mem_extChartAt_target x)).differentiableAt (by simp))
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  change scalarGradientPair h (fun y => a y * f y) k x =
    a (chartInv x (chartPt x x)) * scalarGradientPair h f k x +
      f (chartInv x (chartPt x x)) * scalarGradientPair h a k x at hp
  simpa only [hx] using hp

theorem bernstein_pair_mul_right (h : HermitianField M)
    (k : M.Carrier → ℝ) {a f : M.Carrier → ℝ} (ha : SmoothFn a) (hf : SmoothFn f)
    (x : M.Carrier) :
    scalarGradientPair h k (fun y => a y * f y) x =
      a x * scalarGradientPair h k f x + f x * scalarGradientPair h k a x := by
  rw [scalarGradientPair_symm, bernstein_pair_mul_left h ha hf,
    scalarGradientPair_symm h f k, scalarGradientPair_symm h a k]

theorem bernsteinEnergy_drift_identity (g : SmoothMetric M)
    {v : M.Carrier → ℝ → ℝ} (hv : LeafCandidates.PositiveHeatSolution g.form v)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    laplacian g.form (fun y => bernsteinEnergy g v y t) x -
        deriv (bernsteinEnergy g v x) t -
        (v x t / 2) * scalarGradientPair g.form (fun y => v y t)
          (fun y => bernsteinEnergy g v y t) x =
      bernsteinProfile (v x t) *
        (laplacian g.form (fun y => gradNormSq g.form (fun z => v z t) y) x -
          deriv (fun s => gradNormSq g.form (fun z => v z s) x) t) +
        (1 / 2 - v x t ^ 2 / 4) * bernsteinProfile (v x t) *
          gradNormSq g.form (fun y => v y t) x ^ 2 := by
  let f : M.Carrier → ℝ := fun y => v y t
  let Q : M.Carrier → ℝ := gradNormSq g.form f
  let H : M.Carrier → ℝ := fun y => bernsteinProfile (f y)
  have hf : SmoothFn f := positiveHeatSolution_slice g.form hv ht
  have hQ : SmoothFn Q := smoothSpaceTime_slice (smoothSpaceTime_gradNormSq g hv.1) ht
  have hH : SmoothFn H := smoothFn_scalar_comp hf bernsteinProfile bernsteinProfile_contDiff
  have hHder : DifferentiableAt ℝ bernsteinProfile (f x) :=
    (bernsteinProfile_hasDerivAt (f x)).differentiableAt
  have hLH := laplacian_scalar_comp g.form hf bernsteinProfile x
    (bernsteinProfile_contDiff.contDiffAt.of_le (by simp))
  rw [bernsteinProfile_secondDeriv, bernsteinProfile_deriv,
    scalarGradientPair_eq_twice_gradNormSq g.form hf x] at hLH
  have hPHQ := scalarGradientPair_scalar_comp_left g.form hf Q bernsteinProfile x hHder
  rw [bernsteinProfile_deriv] at hPHQ
  have hPfH : scalarGradientPair g.form f H x =
      f x / 2 * bernsteinProfile (f x) * (2 * Q x) := by
    rw [scalarGradientPair_symm]
    have hh := scalarGradientPair_scalar_comp_left g.form hf f bernsteinProfile x hHder
    rw [bernsteinProfile_deriv, scalarGradientPair_eq_twice_gradNormSq g.form hf x] at hh
    exact hh
  have hPW := bernstein_pair_mul_right g.form f hH hQ x
  rw [hPfH] at hPW
  have hdQ := gradNormSq_time_hasDerivAt g.form hv.1 x ht
  have hdv := positiveHeatSolution_hasDerivAt g.form hv x ht
  have hdW := ((bernsteinProfile_hasDerivAt (v x t)).comp t hdv).mul hdQ
  have hdt : deriv (bernsteinEnergy g v x) t =
      (f x / 2 * bernsteinProfile (f x) * laplacian g.form f x) * Q x +
        H x * deriv (fun s => gradNormSq g.form (fun z => v z s) x) t := by
    rw [hdQ.deriv]
    exact hdW.deriv
  change laplacian g.form (fun y => H y * Q y) x -
      deriv (bernsteinEnergy g v x) t - (f x / 2) *
      scalarGradientPair g.form f (fun y => H y * Q y) x = _
  rw [laplacian_mul g.form hH hQ x, hLH, hdt, hPW]
  change H x * laplacian g.form Q x + Q x * _ +
    scalarGradientPair g.form H Q x - _ - _ = _
  rw [hPHQ]
  dsimp only [H, Q, f]
  ring

theorem bernsteinEnergy_drift (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {v : M.Carrier → ℝ → ℝ} (hv : LeafCandidates.PositiveHeatSolution g.form v)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) (hunit : v x t ^ 2 ≤ 1) :
    bernsteinBeta * bernsteinEnergy g v x t ^ 2 +
        (v x t / 2) * scalarGradientPair g.form (fun y => v y t)
          (fun y => bernsteinEnergy g v y t) x ≤
      laplacian g.form (fun y => bernsteinEnergy g v y t) x -
        deriv (bernsteinEnergy g v x) t := by
  let a := v x t
  let h := bernsteinProfile a
  let q := gradNormSq g.form (fun y => v y t) x
  have hhpos : 0 < h := Real.exp_pos _
  have hhE : h ≤ bernsteinE := bernsteinProfile_le_E hunit
  have hb : bernsteinBeta * h ≤ 1 / 4 := by
    change 1 / (4 * bernsteinE) * h ≤ 1 / 4
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (mul_pos (by norm_num) bernsteinE_pos)).mpr
    nlinarith only [hhE]
  have hc : (1 / 4 : ℝ) ≤ 1 / 2 - a ^ 2 / 4 := by
    dsimp [a]
    linarith
  have hq2 : 0 ≤ h * q ^ 2 := mul_nonneg hhpos.le (sq_nonneg q)
  have hquad : bernsteinBeta * (h * q) ^ 2 ≤ (1 / 2 - a ^ 2 / 4) * h * q ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hb hq2
    have h2 := mul_le_mul_of_nonneg_right hc hq2
    nlinarith only [h1, h2]
  have hsub := heat_energy_subcaloric g hK hRic hv x ht
  have hsub' := mul_nonneg hhpos.le hsub
  have hid := bernsteinEnergy_drift_identity g hv x ht
  change bernsteinBeta * (h * q) ^ 2 + _ ≤ _
  dsimp only [h, a, q] at hquad hsub'
  linarith only [hid, hsub', hquad]

theorem bernsteinAuxiliary_slice (g : SmoothMetric M)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Set.Ioi 0))
    (τ s : ℝ) (ht : 0 < τ + s) :
    SmoothFn (fun y => bernsteinAuxiliary g v τ y s) := by
  intro a
  exact contDiffOn_const.mul ((smoothSpaceTime_slice (bernsteinEnergy_smoothSpaceTime g hv) ht) a)

theorem bernsteinAuxiliary_time_hasDerivAt (g : SmoothMetric M)
    {v : M.Carrier → ℝ → ℝ} (hv : SmoothSpaceTime v (Set.Ioi 0))
    (τ : ℝ) (x : M.Carrier) {s : ℝ} (ht : 0 < τ + s) :
    HasDerivAt (bernsteinAuxiliary g v τ x)
      (bernsteinEnergy g v x (τ + s) +
        s * deriv (bernsteinEnergy g v x) (τ + s)) s := by
  have hd := ((smoothSpaceTime_time_contDiffAt (bernsteinEnergy_smoothSpaceTime g hv)
    x (Ioi_mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hshift : HasDerivAt (fun r => bernsteinEnergy g v x (τ + r))
      (deriv (bernsteinEnergy g v x) (τ + s)) s := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hd.comp s ((hasDerivAt_id s).const_add τ)
  convert (hasDerivAt_id s).mul hshift using 1 <;> first | rfl | (dsimp; ring)

theorem bernsteinAuxiliary_drift (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {v : M.Carrier → ℝ → ℝ} (hv : LeafCandidates.PositiveHeatSolution g.form v)
    {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 < s) (x : M.Carrier)
    (hunit : v x (τ + s) ^ 2 ≤ 1) :
    bernsteinBeta * bernsteinAuxiliary g v τ x s ^ 2 / s +
        (v x (τ+s) / 2) * scalarGradientPair g.form (fun y => v y (τ+s))
          (fun y => bernsteinAuxiliary g v τ y s) x - bernsteinAuxiliary g v τ x s / s ≤
      laplacian g.form (fun y => bernsteinAuxiliary g v τ y s) x -
        deriv (bernsteinAuxiliary g v τ x) s := by
  have ht : 0 < τ + s := add_pos_of_nonneg_of_pos hτ hs
  have hW := smoothSpaceTime_slice (bernsteinEnergy_smoothSpaceTime g hv.1) ht
  have hh := mul_le_mul_of_nonneg_left (bernsteinEnergy_drift g hK hRic hv x ht hunit) hs.le
  rw [(bernsteinAuxiliary_time_hasDerivAt g hv.1 τ x ht).deriv]
  change bernsteinBeta * (s * bernsteinEnergy g v x (τ+s)) ^ 2 / s +
    (v x (τ+s) / 2) * scalarGradientPair g.form (fun y => v y (τ+s))
      (fun y => s * bernsteinEnergy g v y (τ+s)) x -
      s * bernsteinEnergy g v x (τ+s) / s ≤
    laplacian g.form (fun y => s * bernsteinEnergy g v y (τ+s)) x - _
  rw [laplacian_const_mul g.form hW s x,
    scalarGradientPair_const_mul_right g.form _ hW s x]
  have hsq : bernsteinBeta * (s * bernsteinEnergy g v x (τ+s)) ^ 2 / s =
      s * (bernsteinBeta * bernsteinEnergy g v x (τ+s) ^ 2) := by
    field_simp
  rw [hsq, mul_div_cancel_left₀ _ hs.ne']
  nlinarith only [hh]

end Yau.LeafProofs.L24Aux
