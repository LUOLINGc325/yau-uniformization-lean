import Yau.LeafProofs.L12

noncomputable section
open MeasureTheory Filter
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L12Aux

section MatrixJacobi
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrixInverse_entries_differentiableAt {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun w => (A w)⁻¹ i j) z := by
  letI : NormedAddCommGroup (Matrix ι ι ℝ) :=
    inferInstanceAs (NormedAddCommGroup (ι → ι → ℝ))
  letI : NormedSpace ℝ (Matrix ι ι ℝ) :=
    inferInstanceAs (NormedSpace ℝ (ι → ι → ℝ))
  have hAmat : DifferentiableAt ℝ A z :=
    differentiableAt_pi.mpr (fun i => differentiableAt_pi.mpr (hA i))
  have hdetSmooth : ContDiff ℝ ∞ (fun B : Matrix ι ι ℝ => B.det) := by
    rw [← contDiffOn_univ]
    exact SharedCalculus.contDiffOn_matrix_det (fun i j => by fun_prop)
  have hO : IsOpen {B : Matrix ι ι ℝ | B.det ≠ 0} :=
    isOpen_ne_fun hdetSmooth.continuous continuous_const
  have hInvSmooth : ContDiffOn ℝ ∞ (fun B : Matrix ι ι ℝ => B⁻¹ i j)
      {B : Matrix ι ι ℝ | B.det ≠ 0} :=
    SharedCalculus.contDiffOn_matrix_inv (A := fun B : Matrix ι ι ℝ => B) (fun i j => by fun_prop) (fun B hB => hB) i j
  exact ((hInvSmooth.contDiffAt (hO.mem_nhds hdet)).differentiableAt (by simp)).comp z hAmat

theorem matrixDirectionalDerivative_inv {A : E → Matrix ι ι ℝ} {z : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun w => A w i j) z)
    (hdet : (A z).det ≠ 0) (v : E) :
    matrixDirectionalDerivative (fun w => (A w)⁻¹) z v =
      -((A z)⁻¹ * matrixDirectionalDerivative A z v * (A z)⁻¹) := by
  letI : NormedAddCommGroup (Matrix ι ι ℝ) :=
    inferInstanceAs (NormedAddCommGroup (ι → ι → ℝ))
  letI : NormedSpace ℝ (Matrix ι ι ℝ) :=
    inferInstanceAs (NormedSpace ℝ (ι → ι → ℝ))
  have hAmat : DifferentiableAt ℝ A z :=
    differentiableAt_pi.mpr (fun i => differentiableAt_pi.mpr (hA i))
  have hdcont : ContinuousAt (fun w => (A w).det) z :=
    (continuous_id.matrix_det).continuousAt.comp hAmat.continuousAt
  have hn : ∀ᶠ w in 𝓝 z, (A w).det ≠ 0 :=
    hdcont.eventually (eventually_ne_nhds hdet)
  have heq : (fun w => A w * (A w)⁻¹) =ᶠ[𝓝 z] (fun _ => (1 : Matrix ι ι ℝ)) := by
    filter_upwards [hn] with w hw
    exact Matrix.mul_nonsing_inv (A w) (isUnit_iff_ne_zero.mpr hw)
  have hprod := matrixDirectionalDerivative_congr heq v
  rw [matrixDirectionalDerivative_mul hA (matrixInverse_entries_differentiableAt hA hdet) v,
    matrixDirectionalDerivative_const] at hprod
  have hunit : IsUnit (A z).det := isUnit_iff_ne_zero.mpr hdet
  have hsum : (A z)⁻¹ * matrixDirectionalDerivative A z v * (A z)⁻¹ +
      matrixDirectionalDerivative (fun w => (A w)⁻¹) z v = 0 := by
    calc
      _ = (A z)⁻¹ * (matrixDirectionalDerivative A z v * (A z)⁻¹ +
          A z * matrixDirectionalDerivative (fun w => (A w)⁻¹) z v) := by
        rw [mul_add, ← mul_assoc (A z)⁻¹ (A z), Matrix.nonsing_inv_mul (A z) hunit, one_mul]
        simp only [mul_assoc]
      _ = 0 := by rw [hprod, mul_zero]
  exact eq_neg_of_add_eq_zero_right hsum

/-- The logarithmic derivative of a nonsingular Jacobi matrix satisfies the
matrix Riccati equation. This algebraic identity fixes the multiplication order. -/
theorem jacobi_riccati_algebra (A A₁ A₂ R : Matrix ι ι ℝ)
    (hdet : A.det ≠ 0) (hJacobi : A₂ + R * A = 0) :
    (A₂ * A⁻¹ - A₁ * A⁻¹ * A₁ * A⁻¹) + (A₁ * A⁻¹) * (A₁ * A⁻¹) + R = 0 := by
  have h₂ : A₂ = -(R * A) := eq_neg_of_add_eq_zero_left hJacobi
  rw [h₂, neg_mul, mul_assoc R A A⁻¹,
    Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet), mul_one]
  noncomm_ring

/-- The vanishing Jacobi Wronskian makes the radial logarithmic derivative
symmetric, before using any curvature inequality. -/
theorem jacobi_shape_isSymm (A A₁ : Matrix ι ι ℝ) (hdet : A.det ≠ 0)
    (hW : Aᵀ * A₁ = A₁ᵀ * A) : (A₁ * A⁻¹).IsSymm := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hAB : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hunit
  have htr : A⁻¹ᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  have h := congrArg (fun C : Matrix ι ι ℝ => A⁻¹ᵀ * C * A⁻¹) hW
  have hleft : A⁻¹ᵀ * (Aᵀ * A₁) * A⁻¹ = A₁ * A⁻¹ := by
    rw [← mul_assoc A⁻¹ᵀ Aᵀ A₁, htr, one_mul]
  have hright : A⁻¹ᵀ * (A₁ᵀ * A) * A⁻¹ = (A₁ * A⁻¹)ᵀ := by
    rw [mul_assoc A⁻¹ᵀ (A₁ᵀ * A), mul_assoc A₁ᵀ A A⁻¹, hAB, mul_one,
      Matrix.transpose_mul]
  rw [hleft, hright] at h
  exact h.symm


theorem matrixDirectionalDerivative_eq_of_hasDerivAt
    {A : ℝ → Matrix ι ι ℝ} {A₁ : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A₁ i j) t) :
    matrixDirectionalDerivative A t 1 = A₁ := by
  ext i j
  change fderiv ℝ (fun s => A s i j) t 1 = A₁ i j
  simpa using congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) (hA i j).hasFDerivAt.fderiv

/-- Deriving the actual logarithmic-derivative matrix from a Jacobi ODE,
rather than assuming a Riccati equation as additional input. -/
theorem matrixJacobi_riccati_equation
    {A A₁ : ℝ → Matrix ι ι ℝ} {A₂ R : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ i j, HasDerivAt (fun s => A₁ s i j) (A₂ i j) t)
    (hdet : (A t).det ≠ 0) (hJacobi : A₂ + R * A t = 0) :
    matrixDirectionalDerivative (fun s => A₁ s * (A s)⁻¹) t 1 +
      (A₁ t * (A t)⁻¹) * (A₁ t * (A t)⁻¹) + R = 0 := by
  rw [matrixDirectionalDerivative_mul (fun i j => (hA₁ i j).differentiableAt)
    (matrixInverse_entries_differentiableAt (fun i j => (hA i j).differentiableAt) hdet) 1,
    matrixDirectionalDerivative_eq_of_hasDerivAt hA₁,
    matrixDirectionalDerivative_inv (fun i j => (hA i j).differentiableAt) hdet 1,
    matrixDirectionalDerivative_eq_of_hasDerivAt hA]
  simpa only [mul_neg, mul_assoc, sub_eq_add_neg] using
    jacobi_riccati_algebra (A t) (A₁ t) A₂ R hdet hJacobi

theorem matrixJacobi_trace_inequality
    {A A₁ : ℝ → Matrix ι ι ℝ} {A₂ R : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ i j, HasDerivAt (fun s => A₁ s i j) (A₂ i j) t)
    (hdet : (A t).det ≠ 0) (hJacobi : A₂ + R * A t = 0)
    (hW : (A t)ᵀ * A₁ t = (A₁ t)ᵀ * A t) (hRic : 0 ≤ R.trace) :
    Fintype.card ι * (matrixDirectionalDerivative (fun s => A₁ s * (A s)⁻¹) t 1).trace +
      (A₁ t * (A t)⁻¹).trace ^ 2 ≤ 0 :=
  matrixRiccati_trace_inequality _ _ _ (jacobi_shape_isSymm (A t) (A₁ t) hdet hW)
    (matrixJacobi_riccati_equation hA hA₁ hdet hJacobi) hRic

/-- The scalar trace equation for a genuine logarithmic derivative. -/
theorem matrixJacobi_trace_hasDerivAt
    {A A₁ : ℝ → Matrix ι ι ℝ} {A₂ : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ i j, HasDerivAt (fun s => A₁ s i j) (A₂ i j) t)
    (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s => (A₁ s * (A s)⁻¹).trace)
      (matrixDirectionalDerivative (fun s => A₁ s * (A s)⁻¹) t 1).trace t := by
  have hS := matrix_entries_differentiable_mul (fun i j => (hA₁ i j).differentiableAt)
    (matrixInverse_entries_differentiableAt (fun i j => (hA i j).differentiableAt) hdet)
  convert HasDerivAt.sum (u := Finset.univ)
    (fun i _ => (hS i i).hasFDerivAt.hasDerivAt) using 1
  · funext s
    simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_apply]
  · rfl

/-- Jacobi's determinant equation expressed using the same shape trace. -/
theorem matrixJacobi_det_hasDerivAt
    {A : ℝ → Matrix ι ι ℝ} {A₁ : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A₁ i j) t)
    (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s => (A s).det) ((A₁ * (A t)⁻¹).trace * (A t).det) t := by
  letI : NormedAddCommGroup (Matrix ι ι ℝ) :=
    inferInstanceAs (NormedAddCommGroup (ι → ι → ℝ))
  letI : NormedSpace ℝ (Matrix ι ι ℝ) :=
    inferInstanceAs (NormedSpace ℝ (ι → ι → ℝ))
  have hAmat : DifferentiableAt ℝ A t :=
    differentiableAt_pi.mpr (fun i => differentiableAt_pi.mpr (fun j => (hA i j).differentiableAt))
  have hdetSmooth : ContDiff ℝ ∞ (fun B : Matrix ι ι ℝ => B.det) := by
    rw [← contDiffOn_univ]
    exact SharedCalculus.contDiffOn_matrix_det (fun i j => by fun_prop)
  have hd := ((hdetSmooth.contDiffAt.differentiableAt (by simp)).comp t hAmat).hasFDerivAt.hasDerivAt
  convert hd using 1
  · rfl
  · change _ = fderiv ℝ (fun s => (A s).det) t 1
    rw [fderiv_matrix_det_trace (fun i j => (hA i j).differentiableAt) hdet 1]
    simp_rw [fderiv_matrix_row_apply (fun i j => (hA i j).differentiableAt)]
    change _ = (A t).det * Matrix.trace ((A t)⁻¹ * matrixDirectionalDerivative A t 1)
    rw [matrixDirectionalDerivative_eq_of_hasDerivAt hA, Matrix.trace_mul_comm]
    exact mul_comm _ _

/-- The Euclidean comparison for a Jacobi determinant follows from its
actual second-order matrix equation, Wronskian and radial Ricci trace. -/
theorem matrixJacobi_det_ratio_antitone {k : ℕ} {T : ℝ}
    {A A₁ A₂ R : ℝ → Matrix ι ι ℝ}
    (hcard : Fintype.card ι = k + 1)
    (hA : ∀ t ∈ Set.Ioo 0 T, ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ t ∈ Set.Ioo 0 T, ∀ i j, HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t)
    (hdet : ∀ t ∈ Set.Ioo 0 T, 0 < (A t).det)
    (hJacobi : ∀ t ∈ Set.Ioo 0 T, A₂ t + R t * A t = 0)
    (hW : ∀ t ∈ Set.Ioo 0 T, (A t)ᵀ * A₁ t = (A₁ t)ᵀ * A t)
    (hRic : ∀ t ∈ Set.Ioo 0 T, 0 ≤ (R t).trace)
    (hzero : Tendsto (fun t => t ^ 2 * (A₁ t * (A t)⁻¹).trace - (k + 1 : ℕ) * t)
      (𝓝[>] 0) (𝓝 0)) :
    AntitoneOn (fun t => (A t).det / t ^ (k + 1)) (Set.Ioo 0 T) := by
  apply jacobiDensity_ratio_antitone
    (fun t ht => matrixJacobi_det_hasDerivAt (hA t ht) (hdet t ht).ne')
    (fun t ht => (hdet t ht).le)
    (fun t ht => matrixJacobi_trace_hasDerivAt (hA t ht) (hA₁ t ht) (hdet t ht).ne')
    _ hzero
  intro t ht
  simpa only [hcard] using matrixJacobi_trace_inequality (hA t ht) (hA₁ t ht)
    (hdet t ht).ne' (hJacobi t ht) (hW t ht) (hRic t ht)



/-- A Jacobi matrix with regular initial derivative is asymptotic to `t` times
the identity in the actual finite matrix topology. -/
theorem matrixJacobi_normalized_initial_limit {A : ℝ → Matrix ι ι ℝ}
    (hA0 : A 0 = 0)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) ((1 : Matrix ι ι ℝ) i j) 0) :
    Tendsto (fun t => t⁻¹ • A t) (𝓝[>] 0) (𝓝 (1 : Matrix ι ι ℝ)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  simpa only [Matrix.smul_apply, smul_eq_mul, zero_add, hA0,
    Matrix.zero_apply, sub_zero] using (hA i j).tendsto_slope_zero_right

theorem matrixJacobi_normalized_det_initial_limit {A : ℝ → Matrix ι ι ℝ}
    (hA0 : A 0 = 0)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) ((1 : Matrix ι ι ℝ) i j) 0) :
    Tendsto (fun t => (A t).det / t ^ Fintype.card ι) (𝓝[>] 0) (𝓝 1) := by
  have h := (continuous_id.matrix_det).tendsto (1 : Matrix ι ι ℝ) |>.comp
    (matrixJacobi_normalized_initial_limit hA0 hA)
  simpa only [Function.comp_def, id_eq, Matrix.det_smul, Matrix.det_one,
    inv_pow, div_eq_mul_inv, mul_comm] using h

theorem matrixJacobi_det_pos_near_zero {A : ℝ → Matrix ι ι ℝ}
    (hA0 : A 0 = 0)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) ((1 : Matrix ι ι ℝ) i j) 0) :
    ∀ᶠ t in 𝓝[>] 0, 0 < (A t).det := by
  have hnorm := (continuous_id.matrix_det).tendsto (1 : Matrix ι ι ℝ) |>.comp
    (matrixJacobi_normalized_initial_limit hA0 hA)
  have hpos : ∀ᶠ t in 𝓝[>] 0, 0 < (t⁻¹ • A t).det := by
    apply hnorm.eventually
    change Set.Ioi (0 : ℝ) ∈ 𝓝 ((id (1 : Matrix ι ι ℝ)).det)
    rw [id_eq, Matrix.det_one]
    exact Ioi_mem_nhds (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hpos] with t ht hdet
  have hAB : A t = t • (t⁻¹ • A t) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht), one_smul]
  rw [hAB, Matrix.det_smul]
  exact mul_pos (pow_pos ht _) hdet

/-- The regular Jacobi initial conditions give the singular shape-operator
asymptotic needed in Riccati comparison. -/
theorem matrixJacobi_shape_initial_asymptotic
    {A A₁ : ℝ → Matrix ι ι ℝ}
    (hA0 : A 0 = 0)
    (hA : ∀ i j, HasDerivAt (fun t => A t i j) ((1 : Matrix ι ι ℝ) i j) 0)
    (hA₁ : ContinuousAt A₁ 0) (hA₁0 : A₁ 0 = 1) :
    Tendsto (fun t => t ^ 2 * (A₁ t * (A t)⁻¹).trace - (Fintype.card ι : ℝ) * t)
      (𝓝[>] 0) (𝓝 0) := by
  let B : ℝ → Matrix ι ι ℝ := fun t => t⁻¹ • A t
  have hB : Tendsto B (𝓝[>] 0) (𝓝 (1 : Matrix ι ι ℝ)) :=
    matrixJacobi_normalized_initial_limit hA0 hA

  have hBinv : Tendsto (fun t => (B t)⁻¹) (𝓝[>] 0) (𝓝 (1 : Matrix ι ι ℝ)) := by
    have hi := continuousAt_matrix_inv (1 : Matrix ι ι ℝ)
      (by
        rw [Matrix.det_one]
        change ContinuousAt (fun x : ℝ => Ring.inverse x) 1
        simp only [Ring.inverse_eq_inv]
        exact continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0))
    simpa only [inv_one, Function.comp_def] using hi.tendsto.comp hB
  have hdetB : ∀ᶠ t in 𝓝[>] 0, (B t).det ≠ 0 :=
    ((continuous_id.matrix_det).tendsto (1 : Matrix ι ι ℝ) |>.comp hB).eventually
      (eventually_ne_nhds (by simp))
  have hA₁lim : Tendsto A₁ (𝓝[>] 0) (𝓝 (1 : Matrix ι ι ℝ)) := by
    simpa only [hA₁0] using hA₁.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun t => t • (A₁ t * (A t)⁻¹)) =ᶠ[𝓝[>] 0]
      (fun t => A₁ t * (B t)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin, hdetB] with t ht hdet
    have htne : t ≠ 0 := ne_of_gt ht
    have hAB : A t = t • B t := by
      dsimp [B]
      rw [smul_smul, mul_inv_cancel₀ htne, one_smul]
    have hscale : t • (A t)⁻¹ = (B t)⁻¹ := by
      letI : Invertible t := invertibleOfNonzero htne
      rw [hAB, Matrix.inv_smul (B t) t (isUnit_iff_ne_zero.mpr hdet)]
      simp only [smul_smul, invOf_eq_inv, mul_inv_cancel₀ htne, one_smul]
    rw [← Matrix.mul_smul, hscale]
  have hshape : Tendsto (fun t => t • (A₁ t * (A t)⁻¹)) (𝓝[>] 0)
      (𝓝 (1 : Matrix ι ι ℝ)) := by
    apply (tendsto_congr' heq).mpr
    simpa only [one_mul] using hA₁lim.mul hBinv
  have htrace : Tendsto (fun t => (t • (A₁ t * (A t)⁻¹)).trace) (𝓝[>] 0)
      (𝓝 (Fintype.card ι : ℝ)) := by
    simpa only [Matrix.trace_one, Function.comp_def, id_eq] using
      (continuous_id.matrix_trace).tendsto (1 : Matrix ι ι ℝ) |>.comp hshape
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  convert (hid.mul htrace).sub (hid.const_mul (Fintype.card ι : ℝ)) using 1
  · funext t
    simp only [Matrix.trace_smul, smul_eq_mul]
    ring
  · simp


/-- The curvature symmetry and second-order Jacobi equation imply the
conservation law for the Jacobi Wronskian. -/
theorem matrixJacobi_Wronskian_hasDerivAt
    {A A₁ : ℝ → Matrix ι ι ℝ} {A₂ R : Matrix ι ι ℝ} {t : ℝ}
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ i j, HasDerivAt (fun s => A₁ s i j) (A₂ i j) t)
    (hR : R.IsSymm) (hJacobi : A₂ + R * A t = 0) (i j : ι) :
    HasDerivAt (fun s => ((A s)ᵀ * A₁ s - (A₁ s)ᵀ * A s) i j) 0 t := by
  let W := fun s => (A s)ᵀ * A₁ s - (A₁ s)ᵀ * A s
  have hAdiff (i j) := (hA i j).differentiableAt
  have hA₁diff (i j) := (hA₁ i j).differentiableAt
  have hprod := matrix_entries_differentiable_mul
    (A := fun s => (A s)ᵀ) (B := A₁) (fun i j => hAdiff j i) hA₁diff
  have hprod' := matrix_entries_differentiable_mul
    (A := fun s => (A₁ s)ᵀ) (B := A) (fun i j => hA₁diff j i) hAdiff
  have hWdiff (i j) : DifferentiableAt ℝ (fun s => W s i j) t :=
    (hprod i j).sub (hprod' i j)
  have hDW : matrixDirectionalDerivative W t 1 = 0 := by
    dsimp only [W]
    rw [matrixDirectionalDerivative_sub hprod hprod' 1,
      matrixDirectionalDerivative_mul (A := fun s => (A s)ᵀ) (B := A₁)
        (fun i j => hAdiff j i) hA₁diff 1,
      matrixDirectionalDerivative_mul (A := fun s => (A₁ s)ᵀ) (B := A)
        (fun i j => hA₁diff j i) hAdiff 1,
      matrixDirectionalDerivative_transpose, matrixDirectionalDerivative_transpose,
      matrixDirectionalDerivative_eq_of_hasDerivAt hA,
      matrixDirectionalDerivative_eq_of_hasDerivAt hA₁]
    have h₂ : A₂ = -(R * A t) := eq_neg_of_add_eq_zero_left hJacobi
    rw [h₂, Matrix.transpose_neg, Matrix.transpose_mul, hR.eq]
    noncomm_ring
  have hd := (hWdiff i j).hasFDerivAt.hasDerivAt
  change HasDerivAt (fun s => W s i j) (matrixDirectionalDerivative W t 1 i j) t at hd
  simpa only [W, hDW, Matrix.zero_apply] using hd

/-- Regular initial Jacobi data force the Wronskian to vanish throughout the
nonsingular radial interval. -/
theorem matrixJacobi_Wronskian_zero {T : ℝ} {A A₁ A₂ R : ℝ → Matrix ι ι ℝ}
    (hA0 : A 0 = 0) (hcA : ContinuousAt A 0) (hcA₁ : ContinuousAt A₁ 0)
    (hA : ∀ t ∈ Set.Ioo 0 T, ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ t ∈ Set.Ioo 0 T, ∀ i j, HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t)
    (hR : ∀ t ∈ Set.Ioo 0 T, (R t).IsSymm)
    (hJacobi : ∀ t ∈ Set.Ioo 0 T, A₂ t + R t * A t = 0) :
    ∀ t ∈ Set.Ioo 0 T, (A t)ᵀ * A₁ t = (A₁ t)ᵀ * A t := by
  let W := fun s => (A s)ᵀ * A₁ s - (A₁ s)ᵀ * A s
  have hWc : ContinuousAt W 0 := by
    have hAc (i j) : ContinuousAt (fun s => A s i j) 0 :=
      continuousAt_pi.mp (continuousAt_pi.mp hcA i) j
    have hA₁c (i j) : ContinuousAt (fun s => A₁ s i j) 0 :=
      continuousAt_pi.mp (continuousAt_pi.mp hcA₁ i) j
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    simp only [W, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact (tendsto_finsetSum Finset.univ (fun k _ => (hAc k i).mul (hA₁c k j))).sub
      (tendsto_finsetSum Finset.univ (fun k _ => (hA₁c k i).mul (hAc k j)))

  have hWlim : Tendsto W (𝓝[>] 0) (𝓝 (0 : Matrix ι ι ℝ)) := by
    simpa only [W, hA0, Matrix.transpose_zero, zero_mul, mul_zero, sub_zero]
      using hWc.tendsto.mono_left nhdsWithin_le_nhds
  have hconst : ∀ s ∈ Set.Ioo 0 T, ∀ t ∈ Set.Ioo 0 T, W s = W t := by
    intro s hs t ht
    ext i j
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (f := fun r => W r i j)
      (convex_Ioo 0 T).isPreconnected
    · intro r hr
      exact (matrixJacobi_Wronskian_hasDerivAt (hA r hr) (hA₁ r hr)
        (hR r hr) (hJacobi r hr) i j).differentiableAt.differentiableWithinAt
    · intro r hr
      exact (matrixJacobi_Wronskian_hasDerivAt (hA r hr) (hA₁ r hr)
        (hR r hr) (hJacobi r hr) i j).deriv
    · exact hs
    · exact ht
  intro t ht
  have heq : W =ᶠ[𝓝[>] 0] (fun _ => W t) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (ht.1.trans ht.2))] with s hs hsT
    exact hconst s ⟨hs, hsT⟩ t ht
  have hlim : Tendsto W (𝓝[>] 0) (𝓝 (W t)) :=
    (tendsto_congr' heq).mpr tendsto_const_nhds
  have hzero : W t = 0 := tendsto_nhds_unique hlim hWlim
  exact sub_eq_zero.mp hzero

/-- The full scalar Jacobi determinant comparison with its regular initial
conditions; the Riccati inequality and Wronskian are derived internally. -/
theorem matrixJacobi_det_ratio_antitone_of_initial {k : ℕ} {T : ℝ}
    {A A₁ A₂ R : ℝ → Matrix ι ι ℝ}
    (hcard : Fintype.card ι = k + 1)
    (hA0 : A 0 = 0)
    (hAinitial : ∀ i j, HasDerivAt (fun t => A t i j) ((1 : Matrix ι ι ℝ) i j) 0)
    (hcA₁ : ContinuousAt A₁ 0) (hA₁0 : A₁ 0 = 1)
    (hA : ∀ t ∈ Set.Ioo 0 T, ∀ i j, HasDerivAt (fun s => A s i j) (A₁ t i j) t)
    (hA₁ : ∀ t ∈ Set.Ioo 0 T, ∀ i j, HasDerivAt (fun s => A₁ s i j) (A₂ t i j) t)
    (hdet : ∀ t ∈ Set.Ioo 0 T, 0 < (A t).det)
    (hR : ∀ t ∈ Set.Ioo 0 T, (R t).IsSymm)
    (hJacobi : ∀ t ∈ Set.Ioo 0 T, A₂ t + R t * A t = 0)
    (hRic : ∀ t ∈ Set.Ioo 0 T, 0 ≤ (R t).trace) :
    AntitoneOn (fun t => (A t).det / t ^ (k + 1)) (Set.Ioo 0 T) := by
  have hcA : ContinuousAt A 0 := continuousAt_pi.mpr
    (fun i => continuousAt_pi.mpr (fun j => (hAinitial i j).continuousAt))
  apply matrixJacobi_det_ratio_antitone hcard hA hA₁ hdet hJacobi
    (matrixJacobi_Wronskian_zero hA0 hcA hcA₁ hA hA₁ hR hJacobi) hRic
  simpa only [hcard] using matrixJacobi_shape_initial_asymptotic hA0 hAinitial hcA₁ hA₁0

end MatrixJacobi
end Yau.LeafProofs.L12Aux
