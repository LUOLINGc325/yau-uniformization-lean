import spec.CHAIN.LeafObligations

/-! Auxiliary estimates for the two analytic assertions in leaf L09. -/

noncomputable section

open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap Convolution Topology
open LineDeriv

namespace Yau.LeafProofs

theorem sobolevNormSq_nonneg {n : ℕ} (O : Set (ComplexVector n))
    (u : ComplexVector n → ℂ) (s : ℕ) :
    0 ≤ LeafCandidates.sobolevNormSq O u s := by
  apply Finset.sum_nonneg
  intro j _
  exact integral_nonneg fun _ => sq_nonneg _

theorem integral_iteratedFDeriv_sq_le_sobolevNormSq {n s j : ℕ}
    (O : Set (ComplexVector n)) (u : ComplexVector n → ℂ) (hj : j ≤ s) :
    (∫ z in O, ‖iteratedFDeriv ℝ j u z‖ ^ 2 ∂lebesgueC n) ≤
      LeafCandidates.sobolevNormSq O u s := by
  unfold LeafCandidates.sobolevNormSq
  exact Finset.single_le_sum (s := Finset.range (s + 1))
    (f := fun i => ∫ z in O, ‖iteratedFDeriv ℝ i u z‖ ^ 2 ∂lebesgueC n)
    (fun i _ => integral_nonneg fun _ => sq_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

theorem complexVector_finrank_real (n : ℕ) :
    Module.finrank ℝ (ComplexVector n) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex]
  simp [ComplexVector]

def complexVector_realOrthonormalBasis (n : ℕ) :
    OrthonormalBasis (RIdx n) ℝ (ComplexVector n) :=
  (Pi.orthonormalBasis fun _ : Fin n => Complex.orthonormalBasisOneI).reindex
    (Equiv.sigmaEquivProd (Fin n) (Fin 2))

theorem complexVector_realOrthonormalBasis_apply (n : ℕ) (a : RIdx n) :
    complexVector_realOrthonormalBasis n a = realVec a := by
  rcases a with ⟨i, j⟩
  fin_cases j <;> ext l <;>
    simp [complexVector_realOrthonormalBasis, OrthonormalBasis.reindex_apply,
      Pi.orthonormalBasis_apply, Complex.coe_orthonormalBasisOneI, realVec,
      EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]

theorem lebesgueC_eq_volume (n : ℕ) :
    lebesgueC n = (volume : Measure (ComplexVector n)) := by
  let b := complexVector_realOrthonormalBasis n
  have hsum : (fun r : RIdx n → ℝ => ∑ a, r a • realVec a) =
      b.repr.symm ∘ (WithLp.toLp 2 : (RIdx n → ℝ) → EuclideanSpace ℝ (RIdx n)) := by
    funext r
    simpa only [Function.comp_apply, complexVector_realOrthonormalBasis_apply,
      PiLp.toLp_apply, b] using b.sum_repr_symm (WithLp.toLp 2 r)
  have hmp := b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (RIdx n))
  simpa only [lebesgueC, hsum] using hmp.map_eq

theorem integrable_sobolev_weight {n k s : ℕ} (hks : k + n < s) :
    Integrable (fun x : ComplexVector n =>
      (1 + ‖x‖ ^ 2) ^ (-((s : ℝ) - k))) := by
  have hd : (Module.finrank ℝ (ComplexVector n) : ℝ) <
      2 * ((s : ℝ) - k) := by
    rw [complexVector_finrank_real]
    have h : (k : ℝ) + n < s := by exact_mod_cast hks
    push_cast
    linarith
  have h := integrable_rpow_neg_one_add_norm_sq (μ := volume) hd
  convert h using 1
  ext x
  congr 1
  ring

theorem lebesgueC_zero : lebesgueC 0 = Measure.dirac 0 := by
  unfold lebesgueC
  rw [MeasureTheory.Measure.volume_pi_eq_dirac 0, Measure.map_dirac]
  simp

theorem interiorSobolevEmbedding_zero (k s : ℕ) (r R : ℝ)
    (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ComplexVector 0 → ℂ,
      ContDiffOn ℝ ∞ u (Metric.ball 0 R) →
      (∀ j ≤ s, IntegrableOn (fun z => ‖iteratedFDeriv ℝ j u z‖ ^ 2)
        (Metric.ball 0 R) (lebesgueC 0)) →
      ∀ z ∈ Metric.ball (0 : ComplexVector 0) r,
        ‖iteratedFDeriv ℝ k u z‖ ≤ C * Real.sqrt
          (LeafCandidates.sobolevNormSq (Metric.ball (0 : ComplexVector 0) R) u s) := by
  refine ⟨1, one_pos, ?_⟩
  intro u _ _ z _
  have hu : u = fun _ => u 0 := by
    funext x
    congr 1
    exact Subsingleton.elim _ _
  have hz : z = 0 := Subsingleton.elim _ _
  subst z
  rw [one_mul]
  by_cases hk : k = 0
  · subst k
    rw [norm_iteratedFDeriv_zero]
    have h0 : ‖u 0‖ ^ 2 ≤
        LeafCandidates.sobolevNormSq (Metric.ball (0 : ComplexVector 0) R) u s := by
      have := integral_iteratedFDeriv_sq_le_sobolevNormSq
        (Metric.ball (0 : ComplexVector 0) R) u (Nat.zero_le s)
      have hR : (0 : ComplexVector 0) ∈ Metric.ball 0 R :=
        Metric.mem_ball_self (lt_trans hr hrR)
      have hball : Metric.ball (0 : ComplexVector 0) R = Set.univ := by
        ext x
        simp [Subsingleton.elim x 0, hR]
      simpa only [lebesgueC_zero, hball, Measure.restrict_univ,
        integral_dirac, norm_iteratedFDeriv_zero] using this
    calc
      ‖u 0‖ = Real.sqrt (‖u 0‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt h0
  · rw [hu, iteratedFDeriv_const_of_ne hk, Pi.zero_apply, norm_zero]
    exact Real.sqrt_nonneg _

/-- Weighted Cauchy--Schwarz with the precise dimension threshold used by L09. -/
theorem integral_norm_le_weighted_L2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] {a : ℝ}
    (ha : (Module.finrank ℝ E : ℝ) < 2 * a)
    {f : E → ℂ} (hf : AEStronglyMeasurable f μ)
    (henergy : Integrable (fun x => (1 + ‖x‖ ^ 2) ^ a * ‖f x‖ ^ 2) μ) :
    (∫ x, ‖f x‖ ∂μ) ≤
      Real.sqrt (∫ x : E, (1 + ‖x‖ ^ 2) ^ (-a) ∂μ) *
        Real.sqrt (∫ x, (1 + ‖x‖ ^ 2) ^ a * ‖f x‖ ^ 2 ∂μ) := by
  let w : E → ℝ := fun x => (1 + ‖x‖ ^ 2) ^ (a / 2)
  let v : E → ℝ := fun x => (1 + ‖x‖ ^ 2) ^ (-a / 2)
  have hwc : Continuous w := by
    exact (continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun x => Or.inl (ne_of_gt (by positivity : 0 < 1 + ‖x‖ ^ 2)))
  have hvc : Continuous v := by
    exact (continuous_const.add (continuous_norm.pow 2)).rpow_const
      (fun x => Or.inl (ne_of_gt (by positivity : 0 < 1 + ‖x‖ ^ 2)))
  have hw_sq (x : E) : w x ^ 2 = (1 + ‖x‖ ^ 2) ^ a := by
    dsimp [w]
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    ring
  have hv_sq (x : E) : v x ^ 2 = (1 + ‖x‖ ^ 2) ^ (-a) := by
    dsimp [v]
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    ring
  have hwv (x : E) : v x * w x = 1 := by
    dsimp [v, w]
    rw [← Real.rpow_add (by positivity)]
    convert Real.rpow_zero (1 + ‖x‖ ^ 2) using 2 <;> ring
  have hv_int : Integrable (fun x : E => (1 + ‖x‖ ^ 2) ^ (-a)) μ := by
    convert integrable_rpow_neg_one_add_norm_sq (μ := μ) ha using 1
    ext x
    congr 1
    ring
  have hv : MemLp v 2 μ :=
    (memLp_two_iff_integrable_sq hvc.aestronglyMeasurable).mpr (by
      simpa only [hv_sq] using hv_int)
  have hwf : MemLp (fun x => w x * ‖f x‖) 2 μ :=
    (memLp_two_iff_integrable_sq
      (hwc.aestronglyMeasurable.mul hf.norm)).mpr (by
        simpa only [Pi.mul_apply, mul_pow, hw_sq] using henergy)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (f := v) (g := fun x => w x * ‖f x‖)
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (by positivity) _)
    (Filter.Eventually.of_forall fun x =>
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _))
    (by simpa using hv) (by simpa using hwf)
  have hprod : (fun x => v x * (w x * ‖f x‖)) = fun x => ‖f x‖ := by
    funext x
    rw [← mul_assoc, hwv, one_mul]
  simpa only [hprod, Real.rpow_two, hv_sq, mul_pow, hw_sq,
    one_div, Real.sqrt_eq_rpow] using hCS

theorem schwartz_weighted_energy_integrable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : 𝓢(E, ℂ)) (a : ℝ) :
    Integrable (fun x => (1 + ‖x‖ ^ 2) ^ a * ‖f x‖ ^ 2) := by
  have htemp : (fun x : E => (1 + ‖x‖ ^ 2) ^ (a / 2)).HasTemperateGrowth := by
    fun_prop
  let g : 𝓢(E, ℂ) := SchwartzMap.smulLeftCLM ℂ
    (fun x : E => (1 + ‖x‖ ^ 2) ^ (a / 2)) f
  have hg := (memLp_two_iff_integrable_sq_norm
    g.continuous.aestronglyMeasurable).mp (g.memLp 2)
  convert hg using 1
  funext x
  dsimp [g]
  rw [SchwartzMap.smulLeftCLM_apply_apply htemp, norm_smul,
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_pow,
    ← Real.rpow_mul_natCast (by positivity)]
  congr 2
  ring

/-- Fourier inversion and the weighted L² estimate give the global point-value bound. -/
theorem schwartz_norm_le_weighted_fourier_L2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha : (Module.finrank ℝ E : ℝ) < 2 * a)
    (f : 𝓢(E, ℂ)) (x : E) :
    ‖f x‖ ≤ Real.sqrt (∫ ξ : E, (1 + ‖ξ‖ ^ 2) ^ (-a)) *
      Real.sqrt (∫ ξ : E, (1 + ‖ξ‖ ^ 2) ^ a * ‖𝓕 f ξ‖ ^ 2) := by
  calc
    ‖f x‖ = ‖𝓕⁻ (𝓕 f) x‖ := by rw [FourierTransform.fourierInv_fourier_eq]
    _ ≤ ∫ ξ : E, ‖𝓕 f ξ‖ := by
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
      exact Real.norm_fourier_le_integral_norm _ _
    _ ≤ _ := integral_norm_le_weighted_L2 ha
      (𝓕 f).continuous.aestronglyMeasurable (schwartz_weighted_energy_integrable (𝓕 f) a)

theorem fourier_iteratedLineDerivOp_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : 𝓢(E, ℂ)) {j : ℕ} (m : Fin j → E) (ξ : E) :
    ‖𝓕 (∂^{m} f) ξ‖ =
      (2 * Real.pi) ^ j * (∏ i, ‖inner ℝ ξ (m i)‖) * ‖𝓕 f ξ‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have htemp : (inner ℝ · (m 0)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (m 0)).hasTemperateGrowth
    rw [iteratedLineDerivOp_succ_left, SchwartzMap.fourier_lineDerivOp_eq]
    simp only [SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply htemp,
      norm_smul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
    rw [ih (Fin.tail m)]
    rw [Fin.prod_univ_succ, pow_succ]
    simp only [Fin.tail_def, Real.norm_eq_abs]
    ring

theorem sum_fourier_iteratedLineDerivOp_sq
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, ℂ)) (j : ℕ) (ξ : E) :
    (∑ m : Fin j → ι, ‖𝓕 (∂^{fun i => b (m i)} f) ξ‖ ^ 2) =
      (2 * Real.pi) ^ (2 * j) * ‖ξ‖ ^ (2 * j) * ‖𝓕 f ξ‖ ^ 2 := by
  simp_rw [fourier_iteratedLineDerivOp_norm, mul_pow, ← Finset.prod_pow]
  rw [← Finset.sum_mul, ← Finset.mul_sum,
    ← Fintype.sum_pow (fun i : ι => ‖inner ℝ ξ (b i)‖ ^ 2) j,
    b.sum_sq_norm_inner_left]
  simp [← pow_mul, Nat.mul_comm]

theorem schwartz_iteratedFDeriv_sq_integrable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : 𝓢(E, ℂ)) (j : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖ ^ 2) := by
  have hi : Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖) := by
    simpa using f.integrable_pow_mul_iteratedFDeriv volume 0 j
  apply (hi.const_mul (SchwartzMap.seminorm ℝ 0 j f)).mono'
    (((f.smooth ⊤).continuous_iteratedFDeriv (by simp)).norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  change ‖‖iteratedFDeriv ℝ j f x‖ ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := f.norm_iteratedFDeriv_le_seminorm ℝ j x
  nlinarith [norm_nonneg (iteratedFDeriv ℝ j f x)]

/-- Plancherel turns each homogeneous Fourier moment into a derivative energy bound. -/
theorem schwartz_fourier_moment_le
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, ℂ)) (j : ℕ) :
    (2 * Real.pi) ^ (2 * j) * (∫ ξ : E, ‖ξ‖ ^ (2 * j) * ‖𝓕 f ξ‖ ^ 2) ≤
      (Fintype.card ι : ℝ) ^ j * (∫ x : E, ‖iteratedFDeriv ℝ j f x‖ ^ 2) := by
  classical
  have hI (h : 𝓢(E, ℂ)) : Integrable (fun x => ‖h x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm h.continuous.aestronglyMeasurable).mp (h.memLp 2)
  calc
    _ = ∫ ξ : E, (2 * Real.pi) ^ (2 * j) *
        (‖ξ‖ ^ (2 * j) * ‖𝓕 f ξ‖ ^ 2) := (integral_const_mul _ _).symm
    _ = ∫ ξ : E, ∑ m : Fin j → ι,
        ‖𝓕 (∂^{fun i => b (m i)} f) ξ‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with ξ
      simpa only [mul_assoc] using (sum_fourier_iteratedLineDerivOp_sq b f j ξ).symm
    _ = ∑ m : Fin j → ι, ∫ ξ : E,
        ‖𝓕 (∂^{fun i => b (m i)} f) ξ‖ ^ 2 :=
      integral_finsetSum _ (fun m _ => hI _)
    _ = ∑ m : Fin j → ι, ∫ x : E, ‖(∂^{fun i => b (m i)} f) x‖ ^ 2 := by
      simp_rw [SchwartzMap.integral_norm_sq_fourier]
    _ ≤ ∑ _m : Fin j → ι, ∫ x : E, ‖iteratedFDeriv ℝ j f x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m _
      apply integral_mono (hI _) (schwartz_iteratedFDeriv_sq_integrable f j)
      intro x
      dsimp only
      rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
      apply pow_le_pow_left₀ (norm_nonneg _) _
      simpa only [b.norm_eq_one, Finset.prod_const_one, mul_one] using
        (iteratedFDeriv ℝ j f x).le_opNorm (fun i => b (m i))
    _ = _ := by simp

theorem schwartz_norm_pow_mul_sq_integrable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : 𝓢(E, ℂ)) (j : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ (2 * j) * ‖f x‖ ^ 2) := by
  have hi := schwartz_weighted_energy_integrable f (j : ℝ)
  simp only [Real.rpow_natCast] at hi
  refine hi.mono' (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (by positivity)]
  rw [pow_mul]
  gcongr
  linarith

theorem schwartz_fourier_energy_le
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : 𝓢(E, ℂ)) (s : ℕ) :
    (∫ ξ : E, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2) ≤
      (1 + Fintype.card ι : ℝ) ^ s *
        ∑ j ∈ Finset.range (s + 1), ∫ x : E, ‖iteratedFDeriv ℝ j f x‖ ^ 2 := by
  have hM (j : ℕ) : (∫ ξ : E, ‖ξ‖ ^ (2 * j) * ‖𝓕 f ξ‖ ^ 2) ≤
      (Fintype.card ι : ℝ) ^ j * (∫ x : E, ‖iteratedFDeriv ℝ j f x‖ ^ 2) := by
    apply (le_mul_of_one_le_left (integral_nonneg (fun _ => by positivity))
      (one_le_pow₀ (by linarith [Real.pi_gt_three]) : 1 ≤ (2 * Real.pi) ^ (2 * j))).trans
    exact schwartz_fourier_moment_le b f j
  have hexp (ξ : E) : (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2 =
      ∑ j ∈ Finset.range (s + 1),
        (s.choose j : ℝ) * (‖ξ‖ ^ (2 * j) * ‖𝓕 f ξ‖ ^ 2) := by
    rw [add_comm 1 _, add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [one_pow, mul_one, pow_mul]
    ring
  calc
    _ = ∑ j ∈ Finset.range (s + 1), (s.choose j : ℝ) *
        (∫ ξ : E, ‖ξ‖ ^ (2 * j) * ‖𝓕 f ξ‖ ^ 2) := by
      simp_rw [hexp]
      rw [integral_finsetSum _ (fun j _ =>
        (schwartz_norm_pow_mul_sq_integrable (𝓕 f) j).const_mul _)]
      simp_rw [integral_const_mul]
    _ ≤ ∑ j ∈ Finset.range (s + 1), (s.choose j : ℝ) *
        ((Fintype.card ι : ℝ) ^ j * (∫ x : E, ‖iteratedFDeriv ℝ j f x‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hM j) (Nat.cast_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (s + 1), ((s.choose j : ℝ) * (Fintype.card ι : ℝ) ^ j) *
        (∑ l ∈ Finset.range (s + 1), ∫ x : E, ‖iteratedFDeriv ℝ l f x‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.single_le_sum (s := Finset.range (s + 1))
        (f := fun l => ∫ x : E, ‖iteratedFDeriv ℝ l f x‖ ^ 2)
        (fun l _ => integral_nonneg (fun _ => sq_nonneg _)) hj
    _ = _ := by
      rw [← Finset.sum_mul]
      congr 1
      rw [add_comm 1 _, add_pow]
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_comm]

theorem schwartz_sobolev_bound_zero_order (n s : ℕ) (hns : n < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ComplexVector n, ℂ), ∀ x : ComplexVector n,
      ‖f x‖ ≤ C * Real.sqrt (LeafCandidates.sobolevNormSq Set.univ f s) := by
  let b := complexVector_realOrthonormalBasis n
  let A : ℝ := (1 + Fintype.card (RIdx n)) ^ s
  let W : ℝ := ∫ ξ : ComplexVector n, (1 + ‖ξ‖ ^ 2) ^ (-(s : ℝ))
  refine ⟨1 + Real.sqrt W * Real.sqrt A, by dsimp [A]; positivity, ?_⟩
  intro f x
  have hd : (Module.finrank ℝ (ComplexVector n) : ℝ) < 2 * (s : ℝ) := by
    rw [complexVector_finrank_real]
    exact_mod_cast (Nat.mul_lt_mul_of_pos_left hns (by decide : 0 < 2))
  have h0 := schwartz_norm_le_weighted_fourier_L2 hd f x
  have he := schwartz_fourier_energy_le b f s
  simp only [Real.rpow_natCast] at h0
  have he' : (∫ ξ : ComplexVector n, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2) ≤
      A * LeafCandidates.sobolevNormSq Set.univ f s := by
    simpa [A, LeafCandidates.sobolevNormSq, lebesgueC_eq_volume] using he
  calc
    ‖f x‖ ≤ Real.sqrt W *
        Real.sqrt (∫ ξ : ComplexVector n, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2) := h0
    _ ≤ Real.sqrt W * Real.sqrt (A * LeafCandidates.sobolevNormSq Set.univ f s) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he') (Real.sqrt_nonneg _)
    _ = (Real.sqrt W * Real.sqrt A) *
        Real.sqrt (LeafCandidates.sobolevNormSq Set.univ f s) := by
      rw [Real.sqrt_mul (by dsimp [A]; positivity)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith

theorem schwartz_iteratedFDeriv_le_fourier_moment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : 𝓢(E, ℂ)) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k f x‖ ≤
      (2 * Real.pi) ^ k * (∫ ξ : E, ‖ξ‖ ^ k * ‖𝓕 f ξ‖) := by
  let L := -(innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
  let F : 𝓢(E, ℂ) := 𝓕 f
  have heq : (f : E → ℂ) = 𝓕⁻ (F : E → ℂ) := by
    rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]
  have hd := VectorFourier.iteratedFDeriv_fourierIntegral L
    (N := (⊤ : ℕ∞)) (fun j _ => F.integrable_pow_mul volume j)
    F.continuous.aestronglyMeasurable (n := k) (by simp)
  have hkernel := VectorFourier.integrable_fourierPowSMulRight L
    (F.integrable_pow_mul volume k) F.continuous.aestronglyMeasurable
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    rw [one_mul]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    change ‖-(inner ℝ y z)‖ ≤ ‖y‖ * ‖z‖
    simpa only [norm_neg] using norm_inner_le_norm y z
  calc
    ‖iteratedFDeriv ℝ k f x‖ =
        ‖VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂
          (fun ξ => VectorFourier.fourierPowSMulRight L (F : E → ℂ) ξ k) x‖ := by
      conv_lhs => rw [heq]
      change ‖iteratedFDeriv ℝ k
        (VectorFourier.fourierIntegral Real.fourierChar volume L.toLinearMap₁₂ (F : E → ℂ)) x‖ = _
      rw [hd]
    _ ≤ ∫ ξ : E, ‖VectorFourier.fourierPowSMulRight L (F : E → ℂ) ξ k‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ ξ : E, (2 * Real.pi) ^ k * (‖ξ‖ ^ k * ‖𝓕 f ξ‖) := by
      apply integral_mono hkernel.norm (F.integrable_pow_mul volume k |>.const_mul _)
      intro ξ
      apply (VectorFourier.norm_fourierPowSMulRight_le L (F : E → ℂ) ξ k).trans
      calc
        _ ≤ (2 * Real.pi * 1) ^ k * ‖ξ‖ ^ k * ‖𝓕 f ξ‖ := by gcongr
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

theorem schwartz_fourier_L1_moment_le (n k s : ℕ) (hks : k + n < s)
    (f : 𝓢(ComplexVector n, ℂ)) :
    (∫ ξ : ComplexVector n, ‖ξ‖ ^ k * ‖𝓕 f ξ‖) ≤
      Real.sqrt (∫ ξ : ComplexVector n, (1 + ‖ξ‖ ^ 2) ^ (-(s - k : ℕ) : ℝ)) *
        Real.sqrt (∫ ξ : ComplexVector n, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2) := by
  let F : 𝓢(ComplexVector n, ℂ) := 𝓕 f
  let G : ComplexVector n → ℂ := fun ξ => (‖ξ‖ ^ k : ℝ) • F ξ
  have hGc : Continuous G := (continuous_norm.pow k).smul F.continuous
  have hk : k ≤ s := by omega
  have hGn (ξ : ComplexVector n) : ‖G ξ‖ = ‖ξ‖ ^ k * ‖F ξ‖ := by
    simp [G, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ‖ξ‖ ^ k)]
  have hpoint (ξ : ComplexVector n) :
      (1 + ‖ξ‖ ^ 2) ^ (s - k) * ‖G ξ‖ ^ 2 ≤
        (1 + ‖ξ‖ ^ 2) ^ s * ‖F ξ‖ ^ 2 := by
    rw [hGn, mul_pow]
    calc
      _ = (1 + ‖ξ‖ ^ 2) ^ (s - k) * (‖ξ‖ ^ 2) ^ k * ‖F ξ‖ ^ 2 := by ring
      _ ≤ (1 + ‖ξ‖ ^ 2) ^ (s - k) * (1 + ‖ξ‖ ^ 2) ^ k * ‖F ξ‖ ^ 2 := by
        gcongr
        linarith
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hk]
  have hFi : Integrable (fun ξ : ComplexVector n =>
      (1 + ‖ξ‖ ^ 2) ^ s * ‖F ξ‖ ^ 2) := by
    simpa only [Real.rpow_natCast] using schwartz_weighted_energy_integrable F (s : ℝ)
  have hGi : Integrable (fun ξ : ComplexVector n =>
      (1 + ‖ξ‖ ^ 2) ^ (s - k) * ‖G ξ‖ ^ 2) := by
    apply hFi.mono' (by dsimp [G]; fun_prop)
    filter_upwards with ξ
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpoint ξ
  have hd : (Module.finrank ℝ (ComplexVector n) : ℝ) < 2 * (s - k : ℕ) := by
    rw [complexVector_finrank_real]
    have h : 2 * n < 2 * (s - k) := by omega
    exact_mod_cast h
  have hCS := integral_norm_le_weighted_L2 (μ := volume) hd
    (f := G) hGc.aestronglyMeasurable
    (by simpa only [Real.rpow_natCast] using hGi)
  simp only [hGn, Real.rpow_natCast] at hCS
  apply hCS.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  simpa only [hGn] using integral_mono hGi hFi hpoint

theorem schwartz_sobolev_bound (n k s : ℕ) (hks : k + n < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(ComplexVector n, ℂ), ∀ x : ComplexVector n,
      ‖iteratedFDeriv ℝ k f x‖ ≤
        C * Real.sqrt (LeafCandidates.sobolevNormSq Set.univ f s) := by
  let b := complexVector_realOrthonormalBasis n
  let A : ℝ := (1 + Fintype.card (RIdx n)) ^ s
  let W : ℝ := ∫ ξ : ComplexVector n, (1 + ‖ξ‖ ^ 2) ^ (-(s - k : ℕ) : ℝ)
  let B : ℝ := (2 * Real.pi) ^ k * Real.sqrt W
  refine ⟨1 + B * Real.sqrt A, by dsimp [B, A]; positivity, ?_⟩
  intro f x
  have h0 := (schwartz_iteratedFDeriv_le_fourier_moment f k x).trans
    (mul_le_mul_of_nonneg_left (schwartz_fourier_L1_moment_le n k s hks f)
      (by positivity : 0 ≤ (2 * Real.pi) ^ k))
  have he := schwartz_fourier_energy_le b f s
  have he' : (∫ ξ : ComplexVector n, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2) ≤
      A * LeafCandidates.sobolevNormSq Set.univ f s := by
    simpa [A, LeafCandidates.sobolevNormSq, lebesgueC_eq_volume] using he
  calc
    ‖iteratedFDeriv ℝ k f x‖ ≤ B *
        Real.sqrt (∫ ξ : ComplexVector n, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2) := by
      simpa only [B, mul_assoc, W] using h0
    _ ≤ B * Real.sqrt (A * LeafCandidates.sobolevNormSq Set.univ f s) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he') (by dsimp [B]; positivity)
    _ = (B * Real.sqrt A) * Real.sqrt (LeafCandidates.sobolevNormSq Set.univ f s) := by
      rw [Real.sqrt_mul (by dsimp [A]; positivity)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      linarith

/-- The weak-gradient identity applied to a translated, reflected smoothing kernel. -/
theorem weakPlanarGradient_kernel_identity
    {O : Set ℂ} {v : ℂ → ℝ} {g : ℂ → LeafCandidates.RV 2}
    (hg : LeafCandidates.WeakPlanarGradient O v g)
    {κ : ℂ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (x : ℂ) (hO : tsupport (fun y => κ (x - y)) ⊆ O) (i : Fin 2) :
    (∫ y in O, v y * fderiv ℝ κ (x - y) (if i = 0 then 1 else Complex.I)) =
      ∫ y in O, g y i * κ (x - y) := by
  have hφ : ContDiff ℝ ∞ (fun y => κ (x - y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport (fun y => κ (x - y)) := by
    simpa only [Homeomorph.coe_subLeft, Function.comp_def] using
      hcκ.comp_homeomorph (Homeomorph.subLeft x)
  have hd (y e : ℂ) :
      fderiv ℝ (fun y => κ (x - y)) y e = -(fderiv ℝ κ (x - y) e) := by
    have h := ((hκ.differentiable (by simp)).differentiableAt (x := x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub x)
    simpa [Function.comp_def] using congrArg (fun L : ℂ →L[ℝ] ℝ => L e) h.fderiv
  have h := hg.2.2 _ hφ hcφ hO i
  simp_rw [hd, mul_neg, integral_neg] at h
  exact neg_injective h

theorem weakPlanarGradient_mollified_fderiv
    {O : Set ℂ} (hOm : MeasurableSet O) {v : ℂ → ℝ}
    {g : ℂ → LeafCandidates.RV 2}
    (hg : LeafCandidates.WeakPlanarGradient O v g)
    {κ : ℂ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (x : ℂ) (hO : tsupport (fun y => κ (x - y)) ⊆ O) (i : Fin 2) :
    fderiv ℝ (fun z => ∫ y in O, v y * κ (z - y)) x
      (if i = 0 then 1 else Complex.I) =
        ∫ y in O, g y i * κ (x - y) := by
  classical
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hv : Integrable (O.indicator v) := (integrable_indicator_iff hOm).mpr hg.1
  have hconv (z : ℂ) :
      (O.indicator v ⋆[L, volume] κ) z = ∫ y in O, v y * κ (z - y) := by
    rw [convolution_def, ← integral_indicator hOm]
    congr 1
    funext y
    by_cases hy : y ∈ O <;> simp [L, hy]
  have hd := hcκ.hasFDerivAt_convolution_right L hv.locallyIntegrable
    (hκ.of_le (by simp)) x
  rw [show (fun z => ∫ y in O, v y * κ (z - y)) =
      (O.indicator v ⋆[L, volume] κ) from funext (fun z => (hconv z).symm), hd.fderiv,
    convolution_precompR_apply L hv.locallyIntegrable (hcκ.fderiv ℝ)
      (hκ.continuous_fderiv (by simp)), convolution_def]
  have hmul : (fun y => L (O.indicator v y)
      (fderiv ℝ κ (x - y) (if i = 0 then 1 else Complex.I))) =
      O.indicator (fun y => v y *
        fderiv ℝ κ (x - y) (if i = 0 then 1 else Complex.I)) := by
    funext y
    by_cases hy : y ∈ O <;> simp [L, hy]
  rw [hmul, integral_indicator hOm]
  exact weakPlanarGradient_kernel_identity hg hκ hcκ x hO i

theorem integral_fderiv_compactlySupported_eq_zero
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (e : ℂ) :
    (∫ x, fderiv ℝ φ x e) = 0 := by
  have hD : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDi : Integrable (fun x => fderiv ℝ φ x e) :=
    hD.integrable_of_hasCompactSupport (hcφ.fderiv_apply ℝ e)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℂ)) (f := fun _ : ℂ => (1 : ℝ)) (g := φ) (v := e)
    (by simp) (by simpa using hDi)
    (by simpa using hφ.continuous.integrable_of_hasCompactSupport hcφ)
    (fun _ _ => differentiableAt_const _) (fun _ _ => (hφ.differentiable (by simp)).differentiableAt)
  simpa using h

/-- Removing an additive constant preserves the precise weak gradient in the leaf statement. -/
theorem weakPlanarGradient_sub_const
    {O : Set ℂ} (hOfin : volume O ≠ ⊤) {v : ℂ → ℝ}
    {g : ℂ → LeafCandidates.RV 2} (hg : LeafCandidates.WeakPlanarGradient O v g)
    (c : ℝ) : LeafCandidates.WeakPlanarGradient O (fun x => v x - c) g := by
  refine ⟨hg.1.sub (integrableOn_const hOfin), hg.2.1, ?_⟩
  intro φ hφ hcφ hsφ i
  let e : ℂ := if i = 0 then 1 else Complex.I
  have hD : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDi : Integrable (fun x => fderiv ℝ φ x e) :=
    hD.integrable_of_hasCompactSupport (hcφ.fderiv_apply ℝ e)
  obtain ⟨B, hB⟩ := (hcφ.fderiv_apply ℝ e).exists_bound_of_continuous hD
  have hvD : IntegrableOn (fun x => v x * fderiv ℝ φ x e) O :=
    hg.1.mul_bdd hD.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hB)
  have hDzero : (∫ x in O, fderiv ℝ φ x e) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_fderiv_compactlySupported_eq_zero hφ hcφ e
    · intro x hx
      have hxφ : x ∉ tsupport φ := fun h => hx (hsφ h)
      simp [fderiv_of_notMem_tsupport ℝ hxφ]
  change (∫ x in O, (v x - c) * fderiv ℝ φ x e) = _
  simp_rw [sub_mul]
  rw [integral_sub hvD (hDi.restrict.const_mul c), integral_const_mul, hDzero,
    mul_zero, sub_zero]
  exact hg.2.2 φ hφ hcφ hsφ i

theorem contDiff_smul_of_tsupport_subset
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ O) {u : E → F} (hu : ContDiffOn ℝ ∞ u O) :
    ContDiff ℝ ∞ (fun x => χ x • u x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hu.contDiffAt (hO.mem_nhds (hs hx)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

/-- A cutoff chosen before the function, with an open buffer before the outer boundary. -/
theorem exists_sobolev_cutoff (n : ℕ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ χ : ComplexVector n → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Metric.ball 0 R ∧
      ∀ x ∈ Metric.ball (0 : ComplexVector n) r, χ =ᶠ[𝓝 x] 1 := by
  let χ : ContDiffBump (0 : ComplexVector n) :=
    ⟨r, (r + R) / 2, hr, by linarith⟩
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, ?_⟩
  · rw [χ.tsupport_eq]
    apply Metric.closedBall_subset_ball
    dsimp [χ]
    linarith
  · intro x hx
    exact χ.eventuallyEq_one_of_mem_ball hx

theorem schwartz_localization
    {n : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O)
    {u : ComplexVector n → ℂ} (hu : ContDiffOn ℝ ∞ u O) :
    ∃ f : 𝓢(ComplexVector n, ℂ),
      (∀ x, f x = χ x • u x) ∧
      tsupport f ⊆ tsupport χ ∧
      ∀ x, χ =ᶠ[𝓝 x] 1 → ∀ k : ℕ,
        iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k u x := by
  have hcf : HasCompactSupport (fun x => χ x • u x) := hcχ.smul_right
  let f := hcf.toSchwartzMap (contDiff_smul_of_tsupport_subset hO hχ hsχ hu)
  refine ⟨f, fun _ => rfl, ?_, ?_⟩
  · change tsupport (fun x => χ x • u x) ⊆ tsupport χ
    exact tsupport_smul_subset_left χ u
  · intro x hx k
    have heq : (f : ComplexVector n → ℂ) =ᶠ[𝓝 x] u := by
      filter_upwards [hx] with y hy
      change χ y • u y = u y
      simp [hy]
    exact (heq.iteratedFDeriv ℝ k).self_of_nhds

theorem cutoff_derivative_sq_le_sum
    {n s j : ℕ} (hjs : j ≤ s) {O : Set (ComplexVector n)} (hO : IsOpen O)
    {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ) {A : ℝ} (hA : 0 ≤ A)
    (hχA : ∀ i ≤ s, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ A)
    {u : ComplexVector n → ℂ} (hu : ContDiffOn ℝ ∞ u O)
    {x : ComplexVector n} (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ j (fun y => χ y • u y) x‖ ^ 2 ≤
      (A * 2 ^ s) ^ 2 *
        ∑ l ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ l u x‖ ^ 2 := by
  let S : ℝ := ∑ l ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ l u x‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hU (l : ℕ) (hls : l ≤ s) : ‖iteratedFDeriv ℝ l u x‖ ≤ Real.sqrt S := by
    calc
      _ = Real.sqrt (‖iteratedFDeriv ℝ l u x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt S := Real.sqrt_le_sqrt (Finset.single_le_sum
        (s := Finset.range (s + 1)) (f := fun l => ‖iteratedFDeriv ℝ l u x‖ ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_range.mpr (by omega)))
  have hprod := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hu
    hO.uniqueDiffOn hx (n := j) (by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hO hx] at hprod
  have hsum : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  have hb : ‖iteratedFDeriv ℝ j (fun y => χ y • u y) x‖ ≤
      (A * 2 ^ s) * Real.sqrt S := by
    apply hprod.trans
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A * Real.sqrt S := by
        apply Finset.sum_le_sum
        intro i hi
        have his : i ≤ s := by have := Finset.mem_range.mp hi; omega
        gcongr
        · exact hχA i his x
        · exact hU (j - i) (by omega)
      _ = (A * 2 ^ j) * Real.sqrt S := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
        ring
      _ ≤ _ := by gcongr <;> norm_num
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow, Real.sq_sqrt hS] using hsq

theorem cutoff_sobolevNormSq_le
    {n : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    {χ : ComplexVector n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ O) (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ComplexVector n → ℂ,
      ContDiffOn ℝ ∞ u O →
      (∀ j ≤ s, IntegrableOn (fun x => ‖iteratedFDeriv ℝ j u x‖ ^ 2) O (lebesgueC n)) →
      LeafCandidates.sobolevNormSq Set.univ (fun x => χ x • u x) s ≤
        C * LeafCandidates.sobolevNormSq O u s := by
  let χS : 𝓢(ComplexVector n, ℝ) := hcχ.toSchwartzMap hχ
  let A : ℝ := 1 + ∑ i ∈ Finset.range (s + 1), SchwartzMap.seminorm ℝ 0 i χS
  have hA : 0 < A := by
    exact add_pos_of_pos_of_nonneg one_pos
      (Finset.sum_nonneg fun i _ => apply_nonneg _ _)
  have hχA (i : ℕ) (hi : i ≤ s) (x : ComplexVector n) : ‖iteratedFDeriv ℝ i χ x‖ ≤ A := by
    apply (χS.norm_iteratedFDeriv_le_seminorm ℝ i x).trans
    have hh := Finset.single_le_sum (s := Finset.range (s + 1))
      (f := fun i => SchwartzMap.seminorm ℝ 0 i χS)
      (fun i _ => apply_nonneg _ _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    dsimp [A]
    linarith
  let B : ℝ := (A * 2 ^ s) ^ 2
  refine ⟨(s + 1 : ℝ) * B, by dsimp [B]; positivity, ?_⟩
  intro u hu huint
  simp only [lebesgueC_eq_volume] at huint
  have hcF : HasCompactSupport (fun x => χ x • u x) := hcχ.smul_right
  let F : 𝓢(ComplexVector n, ℂ) :=
    hcF.toSchwartzMap (contDiff_smul_of_tsupport_subset hO hχ hsχ hu)
  let N : ℝ := ∑ l ∈ Finset.range (s + 1),
    ∫ x in O, ‖iteratedFDeriv ℝ l u x‖ ^ 2
  have hbound (j : ℕ) (hjs : j ≤ s) :
      (∫ x : ComplexVector n, ‖iteratedFDeriv ℝ j F x‖ ^ 2) ≤ B * N := by
    have hsD : tsupport (iteratedFDeriv ℝ j (fun x => χ x • u x)) ⊆ O :=
      (tsupport_iteratedFDeriv_subset j).trans ((tsupport_smul_subset_left χ u).trans hsχ)
    have hglob : (∫ x : ComplexVector n, ‖iteratedFDeriv ℝ j F x‖ ^ 2) =
        ∫ x in O, ‖iteratedFDeriv ℝ j F x‖ ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : iteratedFDeriv ℝ j (fun x => χ x • u x) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx (hsD h))
      change ‖iteratedFDeriv ℝ j (fun x => χ x • u x) x‖ ^ 2 = 0
      simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [hglob]
    calc
      _ ≤ ∫ x in O, B * (∑ l ∈ Finset.range (s + 1), ‖iteratedFDeriv ℝ l u x‖ ^ 2) := by
        apply integral_mono_ae (schwartz_iteratedFDeriv_sq_integrable F j).restrict
          ((integrable_finsetSum _ (fun l hl => huint l (by
            have := Finset.mem_range.mp hl; omega))).const_mul B)
        filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
        exact cutoff_derivative_sq_le_sum hjs hO hχ hA.le hχA hu hx
      _ = B * N := by
        rw [integral_const_mul, integral_finsetSum _ (fun l hl => huint l (by
          have := Finset.mem_range.mp hl; omega))]
  simp only [LeafCandidates.sobolevNormSq, lebesgueC_eq_volume, Measure.restrict_univ]
  calc
    _ ≤ ∑ j ∈ Finset.range (s + 1), B * N := by
      apply Finset.sum_le_sum
      intro j hj
      exact hbound j (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by simp [N, Nat.cast_add, Nat.cast_one, mul_assoc]

theorem interiorSobolevEmbedding : LeafCandidates.InteriorSobolevEmbedding := by
  intro n k s hks r R hr hrR
  obtain ⟨χ, hχ, hcχ, hsχ, hχone⟩ := exists_sobolev_cutoff n hr hrR
  obtain ⟨C₀, hC₀, hglobal⟩ := schwartz_sobolev_bound n k s hks
  obtain ⟨C₁, hC₁, hcutoff⟩ := cutoff_sobolevNormSq_le Metric.isOpen_ball hχ hcχ hsχ s
  refine ⟨C₀ * Real.sqrt C₁, mul_pos hC₀ (Real.sqrt_pos.mpr hC₁), ?_⟩
  intro u hu huint z hz
  obtain ⟨f, hf, _, hderiv⟩ := schwartz_localization Metric.isOpen_ball hχ hcχ hsχ hu
  have hf_eq : (f : ComplexVector n → ℂ) = fun x => χ x • u x := funext hf
  have hcut : LeafCandidates.sobolevNormSq Set.univ f s ≤
      C₁ * LeafCandidates.sobolevNormSq (Metric.ball 0 R) u s := by
    simpa only [hf_eq] using hcutoff u hu huint
  calc
    ‖iteratedFDeriv ℝ k u z‖ = ‖iteratedFDeriv ℝ k f z‖ := by
      rw [hderiv z (hχone z hz) k]
    _ ≤ C₀ * Real.sqrt (LeafCandidates.sobolevNormSq Set.univ f s) := hglobal f z
    _ ≤ C₀ * Real.sqrt (C₁ * LeafCandidates.sobolevNormSq (Metric.ball 0 R) u s) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcut) hC₀.le
    _ = _ := by
      rw [Real.sqrt_mul hC₁.le]
      ring

theorem planar_potential_kernel_integrable (r : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (-(3 / 2 : ℝ))) (Metric.ball 0 r) volume := by
  apply integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := (3 / 2 : ℝ))
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex])
  · filter_upwards with z
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

theorem planar_potential_kernel_memLp (r : ℝ) :
    MemLp (fun z : ℂ => ‖z‖ ^ (-1 : ℝ)) (ENNReal.ofReal (3 / 2))
      (volume.restrict (Metric.ball 0 r)) := by
  have hm : AEStronglyMeasurable (fun z : ℂ => ‖z‖ ^ (-1 : ℝ)) volume :=
    (measurable_norm.pow_const _).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm.restrict (by norm_num) (by norm_num)).mp
  have hi := planar_potential_kernel_integrable r
  unfold IntegrableOn at hi
  convert hi using 1
  funext z
  rw [ENNReal.toReal_ofReal (by norm_num),
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

theorem planar_potential_holder (r : ℝ) {g : ℂ → LeafCandidates.RV 2}
    (hg : MemLp g 3 (volume.restrict (Metric.ball 0 r))) :
    (∫ z in Metric.ball 0 r, ‖g z‖ * ‖z‖ ^ (-1 : ℝ)) ≤
      (eLpNorm g 3 (volume.restrict (Metric.ball 0 r))).toReal *
        (eLpNorm (fun z : ℂ => ‖z‖ ^ (-1 : ℝ)) (ENNReal.ofReal (3 / 2))
          (volume.restrict (Metric.ball 0 r))).toReal := by
  have hpq : (3 : ℝ).HolderConjugate (3 / 2) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hK := planar_potential_kernel_memLp r
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun z : ℂ => norm_nonneg (g z))
    (Filter.Eventually.of_forall fun z : ℂ => Real.rpow_nonneg (norm_nonneg z) (-1))
    (by simpa using hg.norm) hK
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hg.aestronglyMeasurable, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hK.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_div] using hCS

theorem planar_linear_norm_eq_gradient (L : ℂ →L[ℝ] ℝ) :
    ‖L‖ = ‖(WithLp.toLp 2 ![L 1, L Complex.I] : LeafCandidates.RV 2)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.orthonormalBasisOneI.norm_dual L, EuclideanSpace.real_norm_sq_eq]
  simp [Complex.coe_orthonormalBasisOneI, Fin.sum_univ_two]

theorem planar_potential_kernel_integral_scale {r : ℝ} (hr : 0 < r) :
    (∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-(3 / 2 : ℝ))) =
      r ^ (1 / 2 : ℝ) * (∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-(3 / 2 : ℝ))) := by
  have hcomp : (∫ z in Metric.ball (0 : ℂ) 1, ‖r • z‖ ^ (-(3 / 2 : ℝ))) =
      r ^ (-(3 / 2 : ℝ)) * (∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-(3 / 2 : ℝ))) := by
    simp_rw [norm_smul, Real.norm_of_nonneg hr.le,
      Real.mul_rpow hr.le (norm_nonneg _)]
    rw [integral_const_mul]
  have hchange := Measure.setIntegral_comp_smul_of_pos (volume : Measure ℂ)
    (fun z : ℂ => ‖z‖ ^ (-(3 / 2 : ℝ))) (Metric.ball 0 1) hr
  rw [hcomp] at hchange
  simp only [Complex.finrank_real_complex, smul_ball hr.ne', smul_zero,
    Real.norm_of_nonneg hr.le, mul_one, smul_eq_mul] at hchange
  calc
    _ = r ^ 2 * ((r ^ 2)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) r, ‖z‖ ^ (-(3 / 2 : ℝ)))) := by
      field_simp
    _ = r ^ 2 * (r ^ (-(3 / 2 : ℝ)) *
        (∫ z in Metric.ball (0 : ℂ) 1, ‖z‖ ^ (-(3 / 2 : ℝ)))) := by rw [← hchange]
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_natCast r 2, ← Real.rpow_add hr]
      norm_num

theorem planar_potential_kernel_norm_scale {r : ℝ} (hr : 0 < r) :
    (eLpNorm (fun z : ℂ => ‖z‖ ^ (-1 : ℝ)) (ENNReal.ofReal (3 / 2))
      (volume.restrict (Metric.ball 0 r))).toReal =
      r ^ (1 / 3 : ℝ) *
        (eLpNorm (fun z : ℂ => ‖z‖ ^ (-1 : ℝ)) (ENNReal.ofReal (3 / 2))
          (volume.restrict (Metric.ball 0 1))).toReal := by
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (planar_potential_kernel_memLp r).aestronglyMeasurable,
    toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (planar_potential_kernel_memLp 1).aestronglyMeasurable]
  simp_rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _), neg_one_mul]
  rw [planar_potential_kernel_integral_scale hr,
    Real.mul_rpow (Real.rpow_nonneg hr.le _) (integral_nonneg fun _ => by positivity),
    ← Real.rpow_mul hr.le]
  norm_num

theorem smooth_planar_segment_integral
    {O : Set ℂ} (hO : IsOpen O) (hconv : Convex ℝ O) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    u y - u x = ∫ t : ℝ in 0..1,
      fderiv ℝ u (x + t • (y - x)) (y - x) := by
  let p : ℝ → ℂ := fun t => x + t • (y - x)
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : p t ∈ O :=
    hconv.add_smul_sub_mem hx hy ht
  have hDc : ContinuousOn (fun t => fderiv ℝ u (p t) (y - x)) (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.clm_apply _ continuousOn_const
    exact (hu.continuousOn_fderiv_of_isOpen hO (by simp)).comp
      (by dsimp [p]; fun_prop) hp
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t => u (p t)) (fderiv ℝ u (p t) (y - x)) t := by
    have hpt : p t ∈ O := hp t (by simpa using ht)
    have hup := (hu.contDiffAt (hO.mem_nhds hpt)).differentiableAt (by simp)
    apply hup.hasFDerivAt.comp_hasDerivAt t
    simpa [p] using (((hasDerivAt_id t).smul_const (y - x)).const_add x)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hDc.intervalIntegrable_of_Icc zero_le_one)
  simpa [p] using h.symm

theorem smooth_planar_segment_norm_le
    {O : Set ℂ} (hO : IsOpen O) (hconv : Convex ℝ O) {u : ℂ → ℝ}
    (hu : ContDiffOn ℝ ∞ u O) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    |u y - u x| ≤ ∫ t : ℝ in 0..1,
      ‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖ := by
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ O :=
    hconv.add_smul_sub_mem hx hy ht
  have hD : ContinuousOn (fun t : ℝ => fderiv ℝ u (x + t • (y - x))) (Set.Icc 0 1) :=
    (hu.continuousOn_fderiv_of_isOpen hO (by simp)).comp (by fun_prop) hp
  rw [smooth_planar_segment_integral hO hconv hu hx hy, ← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
  apply intervalIntegral.integral_mono_on zero_le_one
    ((hD.clm_apply continuousOn_const).norm.intervalIntegrable_of_Icc zero_le_one)
    ((hD.norm.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one)
  intro t _
  exact (fderiv ℝ u (x + t • (y - x))).le_opNorm (y - x)

theorem planar_segment_cube_integral_le
    {c x : ℂ} {R t : ℝ} (hx : x ∈ Metric.ball c R) (ht : 0 < t) (ht1 : t ≤ 1)
    {h : ℂ → ℝ} (hi : IntegrableOn (fun z => |h z| ^ 3) (Metric.ball c R) volume) :
    (∫ y in Metric.ball c R, |h (x + t • (y - x))| ^ 3) ≤
      (t ^ 2)⁻¹ * (∫ y in Metric.ball c R, |h y| ^ 3) := by
  classical
  let H : ℂ → ℝ := (Metric.ball c R).indicator (fun z => |h z| ^ 3)
  have hH : Integrable H := (integrable_indicator_iff measurableSet_ball).mpr hi
  have hHnonneg (y : ℂ) : 0 ≤ H y := by
    dsimp [H]
    exact Set.indicator_nonneg (fun _ _ => by positivity) y
  have hcomp : Integrable (fun y => H (x + t • (y - x))) := by
    simpa only [sub_eq_add_neg] using ((hH.comp_add_left x).comp_smul ht.ne').comp_add_right (-x)
  calc
    _ = ∫ y in Metric.ball c R, H (x + t • (y - x)) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      dsimp only [H]
      rw [Set.indicator_of_mem ((convex_ball c R).add_smul_sub_mem hx hy ⟨ht.le, ht1⟩)]
    _ ≤ ∫ y : ℂ, H (x + t • (y - x)) :=
      integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall fun _ => hHnonneg _)
        hcomp
    _ = ∫ y : ℂ, H (x + t • y) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self (fun y : ℂ => H (x + t • y)) (-x)
    _ = (t ^ 2)⁻¹ * (∫ y : ℂ, H (x + y)) := by
      simpa only [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t)),
        smul_eq_mul] using Measure.integral_comp_smul (volume : Measure ℂ) (fun y => H (x + y)) t
    _ = _ := by
      rw [integral_add_left_eq_self, integral_indicator measurableSet_ball]

theorem planar_segment_integral_le
    {c x : ℂ} {R t : ℝ} (hx : x ∈ Metric.ball c R) (ht : 0 < t) (ht1 : t ≤ 1)
    {h : ℂ → ℝ} (hc : Continuous h) :
    (∫ y in Metric.ball c R, |h (x + t • (y - x))|) ≤
      (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) * t ^ (-(2 / 3 : ℝ)) *
        (∫ y in Metric.ball c R, |h y| ^ 3) ^ (1 / 3 : ℝ) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball c R) < ⊤)⟩
  have hcc : Continuous (fun y : ℂ => h (x + t • (y - x))) := hc.comp (by fun_prop)
  have hci : IntegrableOn (fun y : ℂ => |h (x + t • (y - x))| ^ 3) (Metric.ball c R) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall c R)
      (hcc.abs.pow 3).continuousOn).mono_set Metric.ball_subset_closedBall
  have hi : IntegrableOn (fun y : ℂ => |h y| ^ 3) (Metric.ball c R) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall c R)
      (hc.abs.pow 3).continuousOn).mono_set Metric.ball_subset_closedBall
  have hM : MemLp (fun y : ℂ => |h (x + t • (y - x))|)
      (ENNReal.ofReal 3) (volume.restrict (Metric.ball c R)) := by
    apply (integrable_norm_rpow_iff hcc.abs.aestronglyMeasurable.restrict
      (by norm_num) (by norm_num)).mp
    unfold IntegrableOn at hci
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_ofNat,
      Real.norm_eq_abs, abs_abs] using hci
  have hpq : (3 : ℝ).HolderConjugate (3 / 2) := by rw [Real.holderConjugate_iff]; norm_num
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun y : ℂ => abs_nonneg (h (x + t • (y - x))))
    (Filter.Eventually.of_forall fun _ : ℂ => zero_le_one) hM
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℂ => (1 : ℝ)) (ENNReal.ofReal (3 / 2))
      (volume.restrict (Metric.ball c R)))
  have hCS' : (∫ y in Metric.ball c R, |h (x + t • (y - x))|) ≤
      (∫ y in Metric.ball c R, |h (x + t • (y - x))| ^ 3) ^ (1 / 3 : ℝ) *
        (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) := by
    simpa [Real.rpow_natCast, integral_const, Measure.real, measureReal_def] using hCS
  have hfactor : ((t ^ 2)⁻¹) ^ (1 / 3 : ℝ) = t ^ (-(2 / 3 : ℝ)) := by
    calc
      _ = (t ^ (-2 : ℝ)) ^ (1 / 3 : ℝ) := by rw [Real.rpow_neg ht.le, Real.rpow_two]
      _ = _ := by rw [← Real.rpow_mul ht.le]; norm_num
  apply hCS'.trans
  calc
    _ ≤ ((t ^ 2)⁻¹ * (∫ y in Metric.ball c R, |h y| ^ 3)) ^ (1 / 3 : ℝ) *
        (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) := by
      gcongr
      exact planar_segment_cube_integral_le hx ht ht1 hi
    _ = _ := by
      rw [Real.mul_rpow (inv_nonneg.mpr (sq_nonneg t))
        (integral_nonneg (fun _ => by positivity)), hfactor]
      ring

theorem planar_segment_product_integrable {h : ℂ → ℝ} (hc : Continuous h)
    (c x : ℂ) (R : ℝ) :
    Integrable (fun p : ℝ × ℂ => |h (x + p.1 • (p.2 - x))|)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Metric.ball c R))) := by
  rw [Measure.prod_restrict]
  have hi : IntegrableOn (fun p : ℝ × ℂ => |h (x + p.1 • (p.2 - x))|)
      (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall c R) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall c R))
      (by fun_prop)
  exact hi.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Metric.ball_subset_closedBall)

theorem planar_path_average_integral_le
    {c x : ℂ} {R : ℝ} (hx : x ∈ Metric.ball c R) {h : ℂ → ℝ} (hc : Continuous h) :
    (∫ t : ℝ in 0..1, ∫ y in Metric.ball c R, |h (x + t • (y - x))|) ≤
      3 * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) *
        (∫ y in Metric.ball c R, |h y| ^ 3) ^ (1 / 3 : ℝ) := by
  have hI : IntervalIntegrable
      (fun t : ℝ => ∫ y in Metric.ball c R, |h (x + t • (y - x))|) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (planar_segment_product_integrable hc c x R).integral_prod_left
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-(2 / 3 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hpowval : (∫ t : ℝ in 0..1, t ^ (-(2 / 3 : ℝ))) = 3 := by
    rw [integral_rpow (Or.inl (by norm_num))]
    norm_num
  calc
    _ ≤ ∫ t : ℝ in 0..1, (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) *
        t ^ (-(2 / 3 : ℝ)) * (∫ y in Metric.ball c R, |h y| ^ 3) ^ (1 / 3 : ℝ) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hI
        ((hpow.const_mul _).mul_const _)
      intro t ht
      exact planar_segment_integral_le hx ht.1 ht.2.le hc
    _ = 3 * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) *
        (∫ y in Metric.ball c R, |h y| ^ 3) ^ (1 / 3 : ℝ) := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hpowval]
      ring

theorem smooth_planar_integrated_deviation_le
    {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u) {c x : ℂ} {R : ℝ}
    (hx : x ∈ Metric.ball c R) :
    (∫ y in Metric.ball c R, |u y - u x|) ≤
      6 * R * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) *
        (∫ y in Metric.ball c R, ‖fderiv ℝ u y‖ ^ 3) ^ (1 / 3 : ℝ) := by
  let h : ℂ → ℝ := fun y => ‖fderiv ℝ u y‖
  have hc : Continuous h := (hu.continuous_fderiv (by simp)).norm
  have hprod : Integrable (fun p : ℝ × ℂ => h (x + p.1 • (p.2 - x)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Metric.ball c R))) := by
    simpa only [h, abs_norm] using planar_segment_product_integrable hc c x R
  have hinner : IntegrableOn (fun y : ℂ => ∫ t : ℝ in 0..1, h (x + t • (y - x)))
      (Metric.ball c R) volume := by
    unfold IntegrableOn
    simpa only [intervalIntegral.integral_of_le zero_le_one] using hprod.integral_prod_right
  have hpoint (y : ℂ) (hy : y ∈ Metric.ball c R) :
      |u y - u x| ≤ 2 * R * (∫ t : ℝ in 0..1, h (x + t • (y - x))) := by
    have hdist : ‖y - x‖ ≤ 2 * R := by
      have hx' := Metric.mem_ball.mp hx
      have hy' := Metric.mem_ball.mp hy
      rw [← dist_eq_norm]
      linarith [dist_triangle y c x, dist_comm c x]
    have hseg := smooth_planar_segment_norm_le isOpen_univ convex_univ hu.contDiffOn
      (Set.mem_univ x) (Set.mem_univ y)
    rw [intervalIntegral.integral_mul_const] at hseg
    calc
      _ ≤ (∫ t : ℝ in 0..1, h (x + t • (y - x))) * ‖y - x‖ := hseg
      _ ≤ _ := by
        rw [mul_comm (2 * R)]
        apply mul_le_mul_of_nonneg_left hdist
        exact intervalIntegral.integral_nonneg_of_forall zero_le_one (fun _ => norm_nonneg _)
  calc
    _ ≤ ∫ y in Metric.ball c R, 2 * R * (∫ t : ℝ in 0..1, h (x + t • (y - x))) := by
      apply integral_mono_ae
        ((ContinuousOn.integrableOn_compact (isCompact_closedBall c R)
          (hu.continuous.sub continuous_const).abs.continuousOn).mono_set Metric.ball_subset_closedBall)
        (hinner.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact hpoint y hy
    _ = 2 * R * (∫ t : ℝ in 0..1, ∫ y in Metric.ball c R, h (x + t • (y - x))) := by
      rw [integral_const_mul]
      simp only [intervalIntegral.integral_of_le zero_le_one]
      congr 1
      exact (integral_integral_swap
        (f := fun (t : ℝ) (y : ℂ) => h (x + t • (y - x))) hprod).symm
    _ ≤ 2 * R * (3 * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) *
        (∫ y in Metric.ball c R, ‖fderiv ℝ u y‖ ^ 3) ^ (1 / 3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by have := Metric.nonempty_ball.mp ⟨x, hx⟩; positivity)
      simpa only [h, abs_norm] using planar_path_average_integral_le hx hc
    _ = _ := by ring

theorem smooth_planar_ball_oscillation_mul_measure
    {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u) {c x y : ℂ} {R : ℝ}
    (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R) :
    volume.real (Metric.ball c R) * |u x - u y| ≤
      12 * R * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) *
        (∫ z in Metric.ball c R, ‖fderiv ℝ u z‖ ^ 3) ^ (1 / 3 : ℝ) := by
  have hint (a : ℂ) : IntegrableOn (fun z => |u z - u a|) (Metric.ball c R) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall c R)
      (hu.continuous.sub continuous_const).abs.continuousOn).mono_set Metric.ball_subset_closedBall
  have htri (z : ℂ) : |u x - u y| ≤ |u z - u x| + |u z - u y| := by
    calc
      _ = |(u x - u z) + (u z - u y)| := by congr 1; ring
      _ ≤ |u x - u z| + |u z - u y| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (u x) (u z)]
  calc
    _ = ∫ _z in Metric.ball c R, |u x - u y| := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]
    _ ≤ ∫ z in Metric.ball c R, (|u z - u x| + |u z - u y|) :=
      integral_mono (integrableOn_const measure_ball_lt_top.ne) ((hint x).add (hint y)) htri
    _ = (∫ z in Metric.ball c R, |u z - u x|) +
        (∫ z in Metric.ball c R, |u z - u y|) := integral_add (hint x) (hint y)
    _ ≤ (6 * R * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) *
        (∫ z in Metric.ball c R, ‖fderiv ℝ u z‖ ^ 3) ^ (1 / 3 : ℝ)) +
        (6 * R * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) *
        (∫ z in Metric.ball c R, ‖fderiv ℝ u z‖ ^ 3) ^ (1 / 3 : ℝ)) :=
      add_le_add (smooth_planar_integrated_deviation_le hu hx)
        (smooth_planar_integrated_deviation_le hu hy)
    _ = _ := by ring

theorem planar_ball_volume_root_bound {c : ℂ} {R : ℝ} (hR : 0 < R) :
    R * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) ≤
      R ^ (1 / 3 : ℝ) * volume.real (Metric.ball c R) := by
  have hvol : volume.real (Metric.ball c R) = R ^ 2 * Real.pi := by
    rw [measureReal_def, Complex.volume_ball]
    simp [hR.le]
  have hMpos : 0 < volume.real (Metric.ball c R) := by rw [hvol]; positivity
  have hM : R ^ 2 ≤ volume.real (Metric.ball c R) := by
    rw [hvol]
    have hp : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hp)]
  have hroot : R ^ (2 / 3 : ℝ) ≤ (volume.real (Metric.ball c R)) ^ (1 / 3 : ℝ) := by
    have hh := Real.rpow_le_rpow (sq_nonneg R) hM (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le] at hh
    norm_num at hh
    exact hh
  have hRroot : R ≤ R ^ (1 / 3 : ℝ) * (volume.real (Metric.ball c R)) ^ (1 / 3 : ℝ) := by
    calc
      R = R ^ (1 / 3 : ℝ) * R ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hR]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hR.le _)
  calc
    _ ≤ (R ^ (1 / 3 : ℝ) * (volume.real (Metric.ball c R)) ^ (1 / 3 : ℝ)) *
        (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hRroot (Real.rpow_nonneg hMpos.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hMpos]
      norm_num

theorem smooth_planar_ball_oscillation_le
    {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u) {c x y : ℂ} {R : ℝ}
    (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R) :
    |u x - u y| ≤ 12 * R ^ (1 / 3 : ℝ) *
      (∫ z in Metric.ball c R, ‖fderiv ℝ u z‖ ^ 3) ^ (1 / 3 : ℝ) := by
  have hR : 0 < R := Metric.nonempty_ball.mp ⟨x, hx⟩
  have hMpos : 0 < volume.real (Metric.ball c R) := by
    rw [measureReal_def, Complex.volume_ball]
    simp [hR.le]
    positivity
  have hcoeff : 12 * R * (volume.real (Metric.ball c R)) ^ (2 / 3 : ℝ) ≤
      12 * R ^ (1 / 3 : ℝ) * volume.real (Metric.ball c R) := by
    convert mul_le_mul_of_nonneg_left (planar_ball_volume_root_bound (c := c) hR)
      (by norm_num : (0 : ℝ) ≤ 12) using 1 <;> ring
  have h := (smooth_planar_ball_oscillation_mul_measure hu hx hy).trans
    (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _))
  apply (mul_le_mul_iff_left₀ hMpos).mp
  convert h using 1 <;> ring

theorem smooth_planar_gradient_memLp {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u) (c : ℂ) (R : ℝ) :
    MemLp (fderiv ℝ u) 3 (volume.restrict (Metric.ball c R)) := by
  have hc := hu.continuous_fderiv (by simp)
  apply (integrable_norm_rpow_iff hc.aestronglyMeasurable.restrict (by norm_num) (by norm_num)).mp
  have hi : IntegrableOn (fun z : ℂ => ‖fderiv ℝ u z‖ ^ 3) (Metric.ball c R) volume :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall c R)
      (hc.norm.pow 3).continuousOn).mono_set Metric.ball_subset_closedBall
  unfold IntegrableOn at hi
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using hi

theorem smooth_planar_ball_oscillation_lp
    {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u) {c x y : ℂ} {R : ℝ}
    (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R) :
    |u x - u y| ≤ 12 * R ^ (1 / 3 : ℝ) *
      (eLpNorm (fderiv ℝ u) 3 (volume.restrict (Metric.ball c R))).toReal := by
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (smooth_planar_gradient_memLp hu c R).aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, one_div] using
    smooth_planar_ball_oscillation_le hu hx hy

theorem smooth_planar_morrey {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u)
    (z₀ : ℂ) {r : ℝ} (hr : 0 < r) {z w : ℂ}
    (hz : z ∈ Metric.ball z₀ r) (hw : w ∈ Metric.ball z₀ r) :
    |u z - u w| ≤ 48 * (eLpNorm (fderiv ℝ u) 3
      (volume.restrict (Metric.ball z₀ (2 * r)))).toReal * ‖z - w‖ ^ (1 / 3 : ℝ) := by
  let N : ℝ := (eLpNorm (fderiv ℝ u) 3 (volume.restrict (Metric.ball z₀ (2 * r)))).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hmono {c : ℂ} {R : ℝ} (hsub : Metric.ball c R ⊆ Metric.ball z₀ (2 * r)) :
      (eLpNorm (fderiv ℝ u) 3 (volume.restrict (Metric.ball c R))).toReal ≤ N :=
    ENNReal.toReal_mono (smooth_planar_gradient_memLp hu z₀ (2 * r)).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono hsub le_rfl))
  by_cases hzw : z = w
  · subst w
    simp
  let d : ℝ := ‖z - w‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hzw)
  have hdα : 0 ≤ d ^ (1 / 3 : ℝ) := Real.rpow_nonneg hd.le _
  by_cases hnear : d < r / 4
  · have hzsmall : z ∈ Metric.ball z (2 * d) := Metric.mem_ball_self (by positivity)
    have hwsmall : w ∈ Metric.ball z (2 * d) := by
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
      change d < 2 * d
      linarith
    have hsub : Metric.ball z (2 * d) ⊆ Metric.ball z₀ (2 * r) := by
      intro q hq
      have hq' := Metric.mem_ball.mp hq
      have hz' := Metric.mem_ball.mp hz
      apply Metric.mem_ball.mpr
      linarith [dist_triangle q z z₀]
    have hpow : (2 * d) ^ (1 / 3 : ℝ) ≤ 2 * d ^ (1 / 3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hd.le]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) hdα
    calc
      _ ≤ 12 * (2 * d) ^ (1 / 3 : ℝ) *
          (eLpNorm (fderiv ℝ u) 3 (volume.restrict (Metric.ball z (2 * d)))).toReal :=
        smooth_planar_ball_oscillation_lp hu hzsmall hwsmall
      _ ≤ 12 * (2 * d ^ (1 / 3 : ℝ)) * N := by gcongr <;> exact hmono hsub
      _ ≤ _ := by change 12 * (2 * d ^ (1 / 3 : ℝ)) * N ≤ 48 * N * d ^ (1 / 3 : ℝ); nlinarith
  · have hpow : r ^ (1 / 3 : ℝ) ≤ 4 * d ^ (1 / 3 : ℝ) := by
      calc
        _ ≤ (4 * d) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow hr.le (by linarith) (by norm_num)
        _ ≤ _ := by
          rw [Real.mul_rpow (by norm_num) hd.le]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) hdα
    calc
      _ ≤ 12 * r ^ (1 / 3 : ℝ) *
          (eLpNorm (fderiv ℝ u) 3 (volume.restrict (Metric.ball z₀ r))).toReal :=
        smooth_planar_ball_oscillation_lp hu hz hw
      _ ≤ 12 * (4 * d ^ (1 / 3 : ℝ)) * N := by
        gcongr
        exact hmono (Metric.ball_subset_ball (by linarith))
      _ = _ := by change 12 * (4 * d ^ (1 / 3 : ℝ)) * N = 48 * N * d ^ (1 / 3 : ℝ); ring

theorem probability_weight_integral_norm_cube_le
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure α} {κ : α → ℝ} (hκ : ∀ a, 0 ≤ κ a) (hκi : Integrable κ μ)
    (hκmass : (∫ a, κ a ∂μ) = 1) {f : α → F} (hf : AEStronglyMeasurable f μ)
    (hcube : Integrable (fun a => κ a * ‖f a‖ ^ 3) μ) :
    ‖∫ a, κ a • f a ∂μ‖ ^ 3 ≤ ∫ a, κ a * ‖f a‖ ^ 3 ∂μ := by
  let U : α → ℝ := fun a => κ a ^ (1 / 3 : ℝ) * ‖f a‖
  let V : α → ℝ := fun a => κ a ^ (2 / 3 : ℝ)
  have hUnonneg (a : α) : 0 ≤ U a := mul_nonneg (Real.rpow_nonneg (hκ a) _) (norm_nonneg _)
  have hVnonneg (a : α) : 0 ≤ V a := Real.rpow_nonneg (hκ a) _
  have hUm : AEStronglyMeasurable U μ :=
    (hκi.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable.mul hf.norm
  have hVm : AEStronglyMeasurable V μ :=
    (hκi.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable
  have hUcube (a : α) : U a ^ 3 = κ a * ‖f a‖ ^ 3 := by
    dsimp [U]
    rw [mul_pow, ← Real.rpow_mul_natCast (hκ a)]
    norm_num
  have hVpow (a : α) : V a ^ (3 / 2 : ℝ) = κ a := by
    dsimp [V]
    rw [← Real.rpow_mul (hκ a)]
    norm_num
  have hprod (a : α) : U a * V a = κ a * ‖f a‖ := by
    have hp : κ a ^ (1 / 3 : ℝ) * κ a ^ (2 / 3 : ℝ) = κ a := by
      rcases eq_or_lt_of_le (hκ a) with hk | hk
      · rw [← hk]
        norm_num
      · rw [← Real.rpow_add hk]
        norm_num
    dsimp [U, V]
    calc
      _ = (κ a ^ (1 / 3 : ℝ) * κ a ^ (2 / 3 : ℝ)) * ‖f a‖ := by ring
      _ = _ := by rw [hp]
  have hUmem : MemLp U (ENNReal.ofReal 3) μ := by
    apply (integrable_norm_rpow_iff hUm (by norm_num) (by norm_num)).mp
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3),
      Real.norm_of_nonneg (hUnonneg _), Real.rpow_ofNat, hUcube] using hcube
  have hVmem : MemLp V (ENNReal.ofReal (3 / 2)) μ := by
    apply (integrable_norm_rpow_iff hVm (by norm_num) (by norm_num)).mp
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
      Real.norm_of_nonneg (hVnonneg _), hVpow] using hκi
  have hpq : (3 : ℝ).HolderConjugate (3 / 2) := by rw [Real.holderConjugate_iff]; norm_num
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hUnonneg) (Filter.Eventually.of_forall hVnonneg) hUmem hVmem
  simp only [hprod, Real.rpow_ofNat, hUcube, hVpow, hκmass, Real.one_rpow, mul_one] at hCS
  have hI : 0 ≤ ∫ a, κ a * ‖f a‖ ^ 3 ∂μ :=
    integral_nonneg fun a => mul_nonneg (hκ a) (pow_nonneg (norm_nonneg _) _)
  have hroot : ((∫ a, κ a * ‖f a‖ ^ 3 ∂μ) ^ (1 / 3 : ℝ)) ^ 3 =
      ∫ a, κ a * ‖f a‖ ^ 3 ∂μ := by
    rw [← Real.rpow_mul_natCast hI]
    norm_num
  have hbound := pow_le_pow_left₀
    (integral_nonneg (fun a => mul_nonneg (hκ a) (norm_nonneg _))) hCS 3
  rw [hroot] at hbound
  apply (pow_le_pow_left₀ (norm_nonneg _) _ 3).trans hbound
  simpa only [norm_smul, Real.norm_of_nonneg (hκ _)] using
    norm_integral_le_integral_norm (fun a => κ a • f a)

theorem probability_convolution_memLp_three_and_norm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {κ : ℂ → ℝ} (hκc : Continuous κ) (hcκ : HasCompactSupport κ)
    (hκ : ∀ y, 0 ≤ κ y) (hκmass : (∫ y, κ y) = 1)
    {g : ℂ → F} (hgi : Integrable g) (hg : MemLp g 3) :
    MemLp (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) 3 ∧
      (eLpNorm (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g) 3 volume).toReal ≤
        (eLpNorm g 3 volume).toReal := by
  have hκi : Integrable κ volume := hκc.integrable_of_hasCompactSupport hcκ
  obtain ⟨B, hB⟩ := hcκ.exists_bound_of_continuous hκc
  have hgCube : Integrable (fun y => ‖g y‖ ^ 3) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using
      hg.integrable_norm_rpow (by norm_num) (by norm_num)
  let G : ℂ → F := κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] g
  let S : ℂ → ℝ := κ ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y => ‖g y‖ ^ 3)
  have hGc : Continuous G := hcκ.continuous_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hκc hgi.locallyIntegrable
  have hSi : Integrable S := hκi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hgCube
  have hpoint (x : ℂ) : ‖G x‖ ^ 3 ≤ S x := by
    have hm : AEStronglyMeasurable (fun y => g (x - y)) volume :=
      hg.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x)
    have hwi : Integrable (fun y => κ y * ‖g (x - y)‖ ^ 3) :=
      (hgCube.comp_sub_left x).bdd_mul hκi.aestronglyMeasurable (Filter.Eventually.of_forall hB)
    simpa only [G, S, convolution_def, ContinuousLinearMap.lsmul_apply,
      ContinuousLinearMap.mul_apply'] using
      probability_weight_integral_norm_cube_le hκ hκi hκmass hm hwi
  have hGcube : Integrable (fun x => ‖G x‖ ^ 3) := by
    apply hSi.mono' (hGc.norm.pow 3).aestronglyMeasurable
    filter_upwards with x
    change ‖‖G x‖ ^ 3‖ ≤ S x
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact hpoint x
  have hGmem : MemLp G 3 := by
    apply (integrable_norm_rpow_iff hGc.aestronglyMeasurable (by norm_num) (by norm_num)).mp
    simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using hGcube
  have hS_int : (∫ x, S x) = ∫ x, ‖g x‖ ^ 3 := by
    dsimp [S]
    rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hκi hgCube, hκmass]
    simp
  have hInt : (∫ x, ‖G x‖ ^ 3) ≤ ∫ x, ‖g x‖ ^ 3 := by
    rw [← hS_int]
    exact integral_mono hGcube hSi hpoint
  refine ⟨hGmem, ?_⟩
  change (eLpNorm G 3 volume).toReal ≤ (eLpNorm g 3 volume).toReal
  rw [toReal_eLpNorm, lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hGc.aestronglyMeasurable, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
  exact Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) hInt (by positivity)

theorem weakPlanarGradient_mollified_norm_eq
    {O : Set ℂ} (hOm : MeasurableSet O) {v : ℂ → ℝ} {g : ℂ → LeafCandidates.RV 2}
    (hg : LeafCandidates.WeakPlanarGradient O v g)
    {κ : ℂ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (x : ℂ) (hO : tsupport (fun y => κ (x - y)) ⊆ O) :
    ‖fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator v) x‖ =
      ‖(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator g) x‖ := by
  classical
  have hgi : Integrable (O.indicator g) := (integrable_indicator_iff hOm).mpr hg.2.1
  have hF : (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator v) =
      fun z => ∫ y in O, v y * κ (z - y) := by
    funext z
    rw [convolution_lsmul_swap, ← integral_indicator hOm]
    congr 1
    funext y
    by_cases hy : y ∈ O <;> simp [hy, smul_eq_mul, mul_comm]
  have hiVec : Integrable (fun y => κ (x - y) • O.indicator g y) := by
    simpa only [ConvolutionExistsAt, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply] using hcκ.convolutionExists_right
        (ContinuousLinearMap.lsmul ℝ ℝ |>.flip) hgi.locallyIntegrable hκ.continuous x
  have hcoord (i : Fin 2) : (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator g) x i =
      ∫ y in O, g y i * κ (x - y) := by
    rw [convolution_lsmul_swap]
    change (EuclideanSpace.proj i : LeafCandidates.RV 2 →L[ℝ] ℝ)
      (∫ y, κ (x - y) • O.indicator g y) = _
    rw [← (EuclideanSpace.proj i : LeafCandidates.RV 2 →L[ℝ] ℝ).integral_comp_comm hiVec,
      ← integral_indicator hOm]
    congr 1
    funext y
    by_cases hy : y ∈ O <;> simp [hy, smul_eq_mul, mul_comm]
  have hDF (i : Fin 2) : fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator v) x
      (if i = 0 then 1 else Complex.I) =
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator g) x i := by
    rw [hF]
    exact (weakPlanarGradient_mollified_fderiv hOm hg hκ hcκ x hO i).trans (hcoord i).symm
  rw [planar_linear_norm_eq_gradient]
  congr 1
  ext i
  fin_cases i
  · simpa using hDF 0
  · simpa using hDF 1

theorem translated_kernel_tsupport_subset_ball
    {z₀ x : ℂ} {r r' δ : ℝ} (hr : r' < r) (hδ : δ < 2 * (r - r'))
    (hx : x ∈ Metric.ball z₀ (2 * r')) {κ : ℂ → ℝ}
    (hsκ : tsupport κ ⊆ Metric.closedBall 0 δ) :
    tsupport (fun y => κ (x - y)) ⊆ Metric.ball z₀ (2 * r) := by
  have hs := tsupport_comp_subset_preimage κ
    (show Continuous (fun y : ℂ => x - y) by fun_prop)
  intro y hy
  have hκy : x - y ∈ tsupport κ := by
    apply hs
    simpa only [Function.comp_def] using hy
  have hnorm : ‖x - y‖ ≤ δ := by simpa using hsκ hκy
  have hdist : dist y x ≤ δ := by simpa [dist_eq_norm, norm_sub_rev] using hnorm
  have hx' := Metric.mem_ball.mp hx
  apply Metric.mem_ball.mpr
  linarith [dist_triangle y x z₀]

theorem weakPlanarGradient_mollified_norm_bound
    {O A : Set ℂ} (hOm : MeasurableSet O) (hAm : MeasurableSet A)
    {v : ℂ → ℝ} {g : ℂ → LeafCandidates.RV 2}
    (hg : LeafCandidates.WeakPlanarGradient O v g) (hgp : MemLp g 3 (volume.restrict O))
    {κ : ℂ → ℝ} (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hκnonneg : ∀ y, 0 ≤ κ y) (hκmass : (∫ y, κ y) = 1)
    (hsκ : ∀ x ∈ A, tsupport (fun y => κ (x - y)) ⊆ O) :
    ContDiff ℝ ∞ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator v) ∧
      (eLpNorm (fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator v)) 3
        (volume.restrict A)).toReal ≤ (eLpNorm g 3 (volume.restrict O)).toReal := by
  classical
  have hvi : Integrable (O.indicator v) := (integrable_indicator_iff hOm).mpr hg.1
  have hgi : Integrable (O.indicator g) := (integrable_indicator_iff hOm).mpr hg.2.1
  have hgp0 : MemLp (O.indicator g) 3 :=
    (memLp_indicator_iff_restrict hOm.nullMeasurableSet).mpr hgp
  have hF := hcκ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ hvi.locallyIntegrable
  have hG := hcκ.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ.continuous hgi.locallyIntegrable
  have hYoung := probability_convolution_memLp_three_and_norm_le hκ.continuous hcκ
    hκnonneg hκmass hgi hgp0
  have hnormeq :
      eLpNorm (fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator v)) 3 (volume.restrict A) =
        eLpNorm (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator g) 3 (volume.restrict A) := by
    apply eLpNorm_congr_norm_ae (hF.continuous_fderiv (by simp)).aestronglyMeasurable.restrict
      hG.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem hAm] with x hx
    exact weakPlanarGradient_mollified_norm_eq hOm hg hκ hcκ x (hsκ x hx)
  refine ⟨hF, ?_⟩
  rw [hnormeq]
  calc
    _ ≤ (eLpNorm (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator g) 3 volume).toReal :=
      ENNReal.toReal_mono hYoung.1.eLpNorm_ne_top (eLpNorm_mono_measure _ Measure.restrict_le_self)
    _ ≤ (eLpNorm (O.indicator g) 3 volume).toReal := hYoung.2
    _ = _ := congrArg ENNReal.toReal
      (eLpNorm_indicator_eq_eLpNorm_restrict hOm.nullMeasurableSet)

theorem mollified_indicator_tendsto
    {O : Set ℂ} (hO : IsOpen O) {v : ℂ → ℝ} (hv : ContinuousOn v O)
    (hvi : IntegrableOn v O volume) {φ : ℕ → ContDiffBump (0 : ℂ)}
    (hφ : Filter.Tendsto (fun m => (φ m).rOut) Filter.atTop (𝓝 0))
    {x : ℂ} (hx : x ∈ O) :
    Filter.Tendsto
      (fun m => ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] O.indicator v) x)
      Filter.atTop (𝓝 (v x)) := by
  classical
  have hi : Integrable (O.indicator v) := (integrable_indicator_iff hO.measurableSet).mpr hvi
  have heq : O.indicator v =ᶠ[𝓝 x] v := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy v
  have hvx : Filter.Tendsto (O.indicator v) (𝓝 x) (𝓝 (v x)) :=
    Filter.Tendsto.congr' heq.symm (hv.continuousAt (hO.mem_nhds hx)).tendsto
  exact ContDiffBump.convolution_tendsto_right (μ := volume) (φ := φ)
    (g := fun _ : ℕ => O.indicator v) (k := fun _ => x) hφ
    (Filter.Eventually.of_forall fun _ => hi.aestronglyMeasurable)
    (hvx.comp Filter.tendsto_snd) tendsto_const_nhds

theorem planarMorrey : LeafCandidates.PlanarMorrey := by
  refine ⟨48, by norm_num, ?_⟩
  intro z₀ r hr v g hv hg hgp z hz w hw
  let a : ℝ := max (max (dist z z₀) (dist w z₀)) (r / 2)
  have har : a < r := by
    exact max_lt (max_lt (Metric.mem_ball.mp hz) (Metric.mem_ball.mp hw)) (by linarith)
  obtain ⟨r', har', hr'r⟩ := exists_between har
  have hr' : 0 < r' := by
    have hh : r / 2 ≤ a := le_max_right _ _
    linarith
  have hz' : z ∈ Metric.ball z₀ r' := Metric.mem_ball.mpr
    (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) har')
  have hw' : w ∈ Metric.ball z₀ r' := Metric.mem_ball.mpr
    (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) har')
  let δ : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hδpos (m : ℕ) : 0 < δ m := by dsimp [δ]; positivity
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun m =>
    ⟨δ m / 2, δ m, by have := hδpos m; linarith, by have := hδpos m; linarith⟩
  have hφ : Filter.Tendsto (fun m => (φ m).rOut) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall : ∀ᶠ m in Filter.atTop, δ m < 2 * (r - r') :=
    hφ.eventually (Iio_mem_nhds (by linarith : 0 < 2 * (r - r')))
  have hsκ (m : ℕ) : tsupport ((φ m).normed volume) ⊆ Metric.closedBall 0 (δ m) := by
    rw [(φ m).tsupport_normed_eq]
  have hbound : ∀ᶠ m in Filter.atTop,
      |(((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
          (Metric.ball z₀ (2 * r)).indicator v) z) -
        (((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
          (Metric.ball z₀ (2 * r)).indicator v) w)| ≤
        48 * (eLpNorm g 3 (volume.restrict (Metric.ball z₀ (2 * r)))).toReal *
          ‖z - w‖ ^ (1 / 3 : ℝ) := by
    filter_upwards [hsmall] with m hm
    have hF := weakPlanarGradient_mollified_norm_bound measurableSet_ball measurableSet_ball hg hgp
      (φ m).contDiff_normed (φ m).hasCompactSupport_normed (φ m).nonneg_normed (φ m).integral_normed
      (fun x hx => translated_kernel_tsupport_subset_ball hr'r hm hx (hsκ m))
    apply (smooth_planar_morrey hF.1 z₀ hr' hz' hw').trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hF.2 (by norm_num : (0 : ℝ) ≤ 48))
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hzO : z ∈ Metric.ball z₀ (2 * r) := Metric.ball_subset_ball (by linarith) hz
  have hwO : w ∈ Metric.ball z₀ (2 * r) := Metric.ball_subset_ball (by linarith) hw
  have hzl := mollified_indicator_tendsto Metric.isOpen_ball hv hg.1 hφ hzO
  have hwl := mollified_indicator_tendsto Metric.isOpen_ball hv hg.1 hφ hwO
  exact le_of_tendsto (hzl.sub hwl).abs hbound

theorem L09 : LeafObligations.L09 := ⟨planarMorrey, interiorSobolevEmbedding⟩

end Yau.LeafProofs
