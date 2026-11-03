import Yau.LeafProofs.L16EnergyEmbedding
import Yau.LeafProofs.L16EnergyForm
import Yau.LeafProofs.L16FiniteVolterra
import Yau.LeafProofs.L16FiniteEnergyIdentity
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Finite Galerkin coordinates in the actual spatial energy graph. -/
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

variable {n m : ℕ} {O : Set (Space n)}

/-- Constants fixed before the forcing and the finite Galerkin space. -/
def energyGalerkinK (lam D : ℝ) : ℝ := 1 + D ^ 2 / lam
def energyGalerkinE (T lam D : ℝ) : ℝ := Real.exp (energyGalerkinK lam D * T)
def energyGalerkinC (T lam D : ℝ) : ℝ :=
  T * energyGalerkinE T lam D +
    (1 + energyGalerkinK lam D * T * energyGalerkinE T lam D) / lam

/-- Reconstruction from finite coefficients in the actual graph space. -/
def energyGalerkinReconstruction (e : Fin m → EnergyGraphSpace O) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EnergyGraphSpace O :=
  ∑ i, (EuclideanSpace.proj i).smulRight (e i)

@[simp] theorem energyGalerkinReconstruction_apply (e : Fin m → EnergyGraphSpace O)
    (c : EuclideanSpace ℝ (Fin m)) :
    energyGalerkinReconstruction e c = ∑ i, c i • e i := by
  simp [energyGalerkinReconstruction]

/-- The forcing coordinates are the genuine `H` inner products. -/
def energyGalerkinForcing (e : Fin m → EnergyGraphSpace O) :
    Lp ℝ 2 (volume.restrict O) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (energyValueProjection O (e i))))

@[simp] theorem energyGalerkinForcing_apply (e : Fin m → EnergyGraphSpace O)
    (F : Lp ℝ 2 (volume.restrict O)) (i : Fin m) :
    energyGalerkinForcing e F i = inner ℝ F (energyValueProjection O (e i)) := by
  simp [energyGalerkinForcing, real_inner_comm]

/-- The Galerkin matrix is assembled from the actual bilinear form and reconstruction. -/
def energyGalerkinMatrix (e : Fin m → EnergyGraphSpace O)
    (B : EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (B.flip (e i)).comp (energyGalerkinReconstruction e)))

@[simp] theorem energyGalerkinMatrix_apply (e : Fin m → EnergyGraphSpace O)
    (B : EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ)
    (c : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    energyGalerkinMatrix e B c i = ∑ j, B (e j) (e i) * c j := by
  simp [energyGalerkinMatrix, map_sum, mul_comm]

theorem energyGalerkin_inner (e : Fin m → EnergyGraphSpace O)
    (he : Orthonormal ℝ (fun i => energyValueProjection O (e i)))
    (c d : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (energyValueProjection O (energyGalerkinReconstruction e c))
      (energyValueProjection O (energyGalerkinReconstruction e d)) = inner ℝ c d := by
  simp only [energyGalerkinReconstruction_apply, map_sum, map_smul]
  simpa [PiLp.inner_apply, mul_comm] using he.inner_sum (fun i => c i) (fun i => d i) Finset.univ

theorem energyGalerkin_norm_sq (e : Fin m → EnergyGraphSpace O)
    (he : Orthonormal ℝ (fun i => energyValueProjection O (e i)))
    (c : EuclideanSpace ℝ (Fin m)) :
    ‖energyValueProjection O (energyGalerkinReconstruction e c)‖ ^ 2 = ‖c‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using energyGalerkin_inner e he c c

theorem energyGalerkinForcing_norm_le (e : Fin m → EnergyGraphSpace O)
    (he : Orthonormal ℝ (fun i => energyValueProjection O (e i)))
    (F : Lp ℝ 2 (volume.restrict O)) : ‖energyGalerkinForcing e F‖ ≤ ‖F‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  simpa [energyGalerkinForcing_apply, real_inner_comm] using
    he.sum_inner_products_le (s := Finset.univ) F

theorem energyGalerkinMatrix_inner (e : Fin m → EnergyGraphSpace O)
    (B : EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ)
    (c d : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (energyGalerkinMatrix e B c) d =
      B (energyGalerkinReconstruction e c) (energyGalerkinReconstruction e d) := by
  simp [energyGalerkinMatrix, energyGalerkinReconstruction_apply, PiLp.inner_apply,
    map_sum]

theorem energyGalerkinForcing_inner (e : Fin m → EnergyGraphSpace O)
    (F : Lp ℝ 2 (volume.restrict O)) (c : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (energyGalerkinForcing e F) c =
      inner ℝ F (energyValueProjection O (energyGalerkinReconstruction e c)) := by
  simp [PiLp.inner_apply, energyGalerkinReconstruction_apply, map_sum,
    inner_sum, inner_smul_right]

def energyGalerkinTestEvaluation (e : Fin m → EnergyGraphSpace O) :
    (EnergyGraphSpace O →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ ℝ (e i)))

instance energyGraphDualToEuclidean_norm (O : Set (Space n)) (m : ℕ) :
    Norm ((EnergyGraphSpace O →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  @ContinuousLinearMap.hasOpNorm ℝ ℝ (EnergyGraphSpace O →L[ℝ] ℝ)
    (EuclideanSpace ℝ (Fin m)) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (RingHom.id ℝ)

instance energyEuclideanToGraphDual_norm (O : Set (Space n)) (m : ℕ) :
    Norm (EuclideanSpace ℝ (Fin m) →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ) :=
  @ContinuousLinearMap.hasOpNorm ℝ ℝ (EuclideanSpace ℝ (Fin m))
    (EnergyGraphSpace O →L[ℝ] ℝ) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance (RingHom.id ℝ)

theorem energyGalerkinMatrix_eq_comp (e : Fin m → EnergyGraphSpace O)
    (B : EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ) :
    energyGalerkinMatrix e B =
      (energyGalerkinTestEvaluation e).comp (B.comp (energyGalerkinReconstruction e)) := by
  ext c i
  simp [energyGalerkinMatrix, energyGalerkinTestEvaluation]

/-- A finite, basis-dependent matrix bound; it does not require stability of an
`H` orthogonal projection in the graph norm. -/
theorem energyGalerkinMatrix_norm_le (e : Fin m → EnergyGraphSpace O)
    (B : EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ) :
    ‖energyGalerkinMatrix e B‖ ≤
      ‖energyGalerkinTestEvaluation e‖ * ‖B‖ * ‖energyGalerkinReconstruction e‖ := by
  have hEval : 0 ≤ ‖energyGalerkinTestEvaluation e‖ :=
    @ContinuousLinearMap.opNorm_nonneg ℝ ℝ (EnergyGraphSpace O →L[ℝ] ℝ)
      (EuclideanSpace ℝ (Fin m)) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) (energyGalerkinTestEvaluation e)
  rw [energyGalerkinMatrix_eq_comp]
  calc
    _ ≤ ‖energyGalerkinTestEvaluation e‖ * ‖B.comp (energyGalerkinReconstruction e)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖energyGalerkinTestEvaluation e‖ *
        (‖B‖ * ‖energyGalerkinReconstruction e‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hEval
    _ = _ := by ring

theorem energyGalerkinMatrix_eq_sum (e : Fin m → EnergyGraphSpace O)
    (B : EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ) :
    energyGalerkinMatrix e B = ∑ i, ∑ j, B (e j) (e i) •
      (EuclideanSpace.proj j).smulRight (EuclideanSpace.single i 1) := by
  ext c i
  simp [energyGalerkinMatrix_apply, Pi.single_apply, mul_comm]

/-- Measurability of the finite matrix requires only its actual scalar entries. -/
theorem energyGalerkinMatrix_aestronglyMeasurable {T : ℝ}
    (e : Fin m → EnergyGraphSpace O)
    (B : ℝ → EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ)
    (hB : ∀ i j, AEStronglyMeasurable (fun t => B t (e j) (e i))
      (volume.restrict (Set.Ioo 0 T))) :
    AEStronglyMeasurable (fun t => energyGalerkinMatrix e (B t))
      (volume.restrict (Set.Ioo 0 T)) := by
  simp_rw [energyGalerkinMatrix_eq_sum]
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
    Finset.aestronglyMeasurable_fun_sum _ (fun j _ =>
      (hB i j).smul aestronglyMeasurable_const))

theorem energyGalerkin_rhs_intervalIntegrable {T M : ℝ} (hT : 0 ≤ T)
    (e : Fin m → EnergyGraphSpace O)
    {F : ℝ → Lp ℝ 2 (volume.restrict O)}
    (hF : MemLp F 2 (volume.restrict (Set.Ioo 0 T)))
    {A : ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ‖A t‖ ≤ M)
    {c : ℝ → EuclideanSpace ℝ (Fin m)} (hc : ContinuousOn c (Set.Icc 0 T)) :
    IntervalIntegrable (fun t => energyGalerkinForcing e (F t) - A t (c t)) volume 0 T := by
  let cc : C(Set.Icc (0 : ℝ) T, EuclideanSpace ℝ (Fin m)) := ⟨_, hc.domRestrict⟩
  have hcm : AEStronglyMeasurable c (volume.restrict (Set.Ioo 0 T)) :=
    (hc.mono Set.Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hm : AEStronglyMeasurable (fun t => A t (c t))
      (volume.restrict (Set.Ioo 0 T)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hA hcm
  have hAc : Integrable (fun t => A t (c t)) (volume.restrict (Set.Ioo 0 T)) := by
    refine (integrable_const (M * ‖cc‖)).mono' hm ?_
    filter_upwards [hAM, ae_restrict_mem measurableSet_Ioo] with t hAt ht
    exact ((A t).le_opNorm (c t)).trans
      (mul_le_mul hAt (cc.norm_coe_le_norm ⟨t, ht.1.le, ht.2.le⟩)
        (norm_nonneg _) ((norm_nonneg _).trans hAt))
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hT).mpr
  exact ((energyGalerkinForcing e).integrable_comp (hF.integrable (by norm_num))).sub hAc

theorem energyGalerkin_pointwise_energy {lam D : ℝ}
    (e : Fin m → EnergyGraphSpace O)
    (B : EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ)
    (F : Lp ℝ 2 (volume.restrict O)) (c : EuclideanSpace ℝ (Fin m))
    (hGard : lam * (∑ i, ‖energyGradientProjection O i (energyGalerkinReconstruction e c)‖ ^ 2) -
      (D ^ 2 / lam) * ‖energyValueProjection O (energyGalerkinReconstruction e c)‖ ^ 2 ≤
        2 * B (energyGalerkinReconstruction e c) (energyGalerkinReconstruction e c)) :
    2 * inner ℝ (energyGalerkinForcing e F - energyGalerkinMatrix e B c) c +
      lam * (∑ i, ‖energyGradientProjection O i (energyGalerkinReconstruction e c)‖ ^ 2) ≤
        energyGalerkinK lam D * ‖energyValueProjection O (energyGalerkinReconstruction e c)‖ ^ 2 +
          ‖F‖ ^ 2 := by
  rw [inner_sub_left, energyGalerkinForcing_inner, energyGalerkinMatrix_inner]
  have hi := real_inner_le_norm F
    (energyValueProjection O (energyGalerkinReconstruction e c))
  have hs := sq_nonneg (‖F‖ - ‖energyValueProjection O (energyGalerkinReconstruction e c)‖)
  dsimp [energyGalerkinK]
  nlinarith

/-- Scalar integral Gronwall, using a classical derivative only for the primitive
of the continuous energy. The forcing enters through the fixed scalar `Q`. -/
theorem energy_integral_gronwall {T K Q : ℝ} (_hT : 0 ≤ T) (hK : 0 < K)
    {y : ℝ → ℝ} (hy : Continuous y)
    (hi : ∀ t ∈ Set.Icc 0 T, y t ≤ K * (∫ s in (0 : ℝ)..t, y s) + Q) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ Real.exp (K * t) * Q := by
  let Y : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, y s
  have hY : ∀ t, HasDerivAt Y (y t) t :=
    fun t => (hy.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hYc : Continuous Y := continuous_iff_continuousAt.mpr
    (fun t => (hY t).continuousAt)
  have hbound : ∀ t ∈ Set.Icc 0 T, Y t ≤ gronwallBound 0 K Q t := by
    simpa only [sub_zero] using
      (le_gronwallBound_of_liminf_deriv_right_le hYc.continuousOn
        (fun t _ r hr => (hY t).hasDerivWithinAt.liminf_right_slope_le hr)
        (by simp [Y]) (fun t ht => hi t ⟨ht.1, ht.2.le⟩))
  intro t ht
  have hyt := hi t ht
  have hbt := hbound t ht
  rw [gronwallBound_of_K_ne_0 hK.ne'] at hbt
  simp only [zero_mul, zero_add] at hbt
  have hm := mul_le_mul_of_nonneg_left hbt hK.le
  have heq : K * (Q / K * (Real.exp (K * t) - 1)) + Q = Real.exp (K * t) * Q := by
    field_simp
    ring
  linarith

theorem energy_integral_gronwall_on {T K Q : ℝ} (hT : 0 ≤ T) (hK : 0 < K)
    {y : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T))
    (hi : ∀ t ∈ Set.Icc 0 T, y t ≤ K * (∫ s in (0 : ℝ)..t, y s) + Q) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ Real.exp (K * t) * Q := by
  let y' : ℝ → ℝ := fun t => y (Set.projIcc 0 T hT t)
  have hy' : Continuous y' :=
    hy.comp_continuous (by fun_prop) (fun t => (Set.projIcc 0 T hT t).property)
  have heq : ∀ t ∈ Set.Icc 0 T, y' t = y t := by
    intro t ht
    simp only [y', Set.projIcc_of_mem hT ht]
  have hint : ∀ t ∈ Set.Icc 0 T,
      (∫ s in (0 : ℝ)..t, y' s) = ∫ s in (0 : ℝ)..t, y s := by
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc 0 t := by simpa only [Set.uIcc_of_le ht.1] using hs
    exact heq s ⟨hs'.1, hs'.2.trans ht.2⟩
  have hres := energy_integral_gronwall hT hK hy' (fun t ht => by
    rw [heq t ht, hint t ht]
    exact hi t ht)
  intro t ht
  simpa only [heq t ht] using hres t ht

theorem energyGalerkinC_pos {T lam D : ℝ} (hT : 0 < T) (hlam : 0 < lam) :
    0 < energyGalerkinC T lam D := by
  have hK : 0 < energyGalerkinK lam D := by dsimp [energyGalerkinK]; positivity
  unfold energyGalerkinC energyGalerkinE
  positivity

/-- The scalar quantitative step of the Galerkin estimate. Only `y` and `z`
are continuous; the nonnegative forcing density is merely integrable. -/
theorem energy_scalar_uniform_bound {T lam D : ℝ} (hT : 0 < T) (hlam : 0 < lam)
    {y z q : ℝ → ℝ} (hy : ContinuousOn y (Set.Icc 0 T))
    (hz : ContinuousOn z (Set.Icc 0 T))
    (hy0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ y t)
    (hz0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ z t)
    (hq : IntervalIntegrable q volume 0 T) (hq0 : ∀ t, 0 ≤ q t)
    (henergy : ∀ t ∈ Set.Icc 0 T,
      y t + lam * (∫ s in (0 : ℝ)..t, z s) ≤
        energyGalerkinK lam D * (∫ s in (0 : ℝ)..t, y s) + ∫ s in (0 : ℝ)..t, q s) :
    (∀ t ∈ Set.Icc 0 T,
      y t ≤ energyGalerkinE T lam D * (∫ s in (0 : ℝ)..T, q s)) ∧
    (∫ s in (0 : ℝ)..T, y s + z s) ≤
      energyGalerkinC T lam D * (∫ s in (0 : ℝ)..T, q s) := by
  let K := energyGalerkinK lam D
  let E := energyGalerkinE T lam D
  let Q := ∫ s in (0 : ℝ)..T, q s
  have hK : 0 < K := by dsimp [K, energyGalerkinK]; positivity
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg_of_forall hT.le hq0
  have hyi : IntervalIntegrable y volume 0 T := hy.intervalIntegrable_of_Icc hT.le
  have hzi : IntervalIntegrable z volume 0 T := hz.intervalIntegrable_of_Icc hT.le
  have hpre : ∀ t ∈ Set.Icc 0 T, y t ≤ K * (∫ s in (0 : ℝ)..t, y s) + Q := by
    intro t ht
    have hzint : 0 ≤ ∫ s in (0 : ℝ)..t, z s :=
      intervalIntegral.integral_nonneg ht.1 (fun s hs => hz0 s ⟨hs.1, hs.2.trans ht.2⟩)
    have hqm : (∫ s in (0 : ℝ)..t, q s) ≤ Q :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Eventually.of_forall hq0) hq
    have he := henergy t ht
    have hlamz := mul_nonneg hlam.le hzint
    dsimp [K, Q] at *
    linarith
  have hpoint : ∀ t ∈ Set.Icc 0 T, y t ≤ E * Q := by
    intro t ht
    calc
      y t ≤ Real.exp (K * t) * Q := energy_integral_gronwall_on hT.le hK hy hpre t ht
      _ ≤ E * Q := by
        apply mul_le_mul_of_nonneg_right _ hQ
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK.le)
  have hyint : (∫ s in (0 : ℝ)..T, y s) ≤ T * E * Q := by
    calc
      _ ≤ ∫ _s in (0 : ℝ)..T, E * Q :=
        intervalIntegral.integral_mono_on hT.le hyi (intervalIntegrable_const) hpoint
      _ = T * E * Q := by rw [intervalIntegral.integral_const]; simp only [sub_zero, smul_eq_mul]; ring
  have hzend := henergy T ⟨hT.le, le_rfl⟩
  have hyT := hy0 T ⟨hT.le, le_rfl⟩
  have hzint : (∫ s in (0 : ℝ)..T, z s) ≤ (1 + K * T * E) / lam * Q := by
    have hm := mul_le_mul_of_nonneg_left hyint hK.le
    apply (mul_le_mul_iff_right₀ hlam).mp
    have heq : lam * ((1 + K * T * E) / lam * Q) = (1 + K * T * E) * Q := by
      field_simp
    rw [heq]
    dsimp [K, E, Q] at *
    nlinarith
  refine ⟨hpoint, ?_⟩
  rw [intervalIntegral.integral_add hyi hzi]
  change (∫ s in (0 : ℝ)..T, y s) + (∫ s in (0 : ℝ)..T, z s) ≤ _
  unfold energyGalerkinC
  change _ ≤ (T * E + (1 + K * T * E) / lam) * Q
  nlinarith

private theorem energy_intervalIntegral_mono_ae_open {a b : ℝ} (hab : a ≤ b)
    {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : f ≤ᵐ[volume.restrict (Set.Ioo a b)] g) :
    (∫ t in a..b, f t) ≤ ∫ t in a..b, g t := by
  simp only [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
  exact integral_mono_ae
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hf)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hg) hfg

/-- Uniform energy estimate derived from the concrete projected integral ODE.
No energy identity is assumed; its proof uses the actual integrable primitive. -/
theorem energyGalerkin_uniform_of_integralODE {T lam D M : ℝ}
    (hT : 0 < T) (hlam : 0 < lam)
    (e : Fin m → EnergyGraphSpace O)
    (he : Orthonormal ℝ (fun i => energyValueProjection O (e i)))
    (B : ℝ → EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ)
    (hEntries : ∀ i j, AEStronglyMeasurable (fun t => B t (e j) (e i))
      (volume.restrict (Set.Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ‖energyGalerkinMatrix e (B t)‖ ≤ M)
    (hGard : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : EnergyGraphSpace O,
      lam * (∑ i, ‖energyGradientProjection O i v‖ ^ 2) -
        (D ^ 2 / lam) * ‖energyValueProjection O v‖ ^ 2 ≤ 2 * B t v v)
    {F : ℝ → Lp ℝ 2 (volume.restrict O)}
    (hF : MemLp F 2 (volume.restrict (Set.Ioo 0 T)))
    {c : ℝ → EuclideanSpace ℝ (Fin m)} (hc : ContinuousOn c (Set.Icc 0 T))
    (hcEq : ∀ t ∈ Set.Icc 0 T, c t = ∫ s in (0 : ℝ)..t,
      energyGalerkinForcing e (F s) - energyGalerkinMatrix e (B s) (c s)) :
    (∀ t ∈ Set.Icc 0 T,
      ‖energyValueProjection O (energyGalerkinReconstruction e (c t))‖ ^ 2 ≤
        energyGalerkinE T lam D *
          (∫ s in Set.Ioo 0 T, ‖F s‖ ^ 2)) ∧
    (∫ s in Set.Ioo 0 T,
      ‖energyValueProjection O (energyGalerkinReconstruction e (c s))‖ ^ 2 +
        ∑ i, ‖energyGradientProjection O i (energyGalerkinReconstruction e (c s))‖ ^ 2) ≤
      energyGalerkinC T lam D * (∫ s in Set.Ioo 0 T, ‖F s‖ ^ 2) := by
  let R := energyGalerkinReconstruction e
  let rhs := fun t => energyGalerkinForcing e (F t) - energyGalerkinMatrix e (B t) (c t)
  let y := fun t => ‖energyValueProjection O (R (c t))‖ ^ 2
  let z := fun t => ∑ i, ‖energyGradientProjection O i (R (c t))‖ ^ 2
  let q := fun t => ‖F t‖ ^ 2
  have hR : ContinuousOn (fun t => R (c t)) (Set.Icc 0 T) :=
    R.continuous.comp_continuousOn hc
  have hy : ContinuousOn y (Set.Icc 0 T) :=
    ((energyValueProjection O).continuous.comp_continuousOn hR).norm.pow 2
  have hz : ContinuousOn z (Set.Icc 0 T) :=
    continuousOn_finsetSum _ (fun i _ =>
      ((energyGradientProjection O i).continuous.comp_continuousOn hR).norm.pow 2)
  have hqi : IntervalIntegrable q volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mpr
      ((memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF)
  have hrhsi : IntervalIntegrable rhs volume 0 T :=
    energyGalerkin_rhs_intervalIntegrable hT.le e hF
      (energyGalerkinMatrix_aestronglyMeasurable e B hEntries) hAM hc
  have hrhs : Integrable rhs (volume.restrict (Set.Ioo 0 T)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le).mp hrhsi
  have hcPrim : ∀ t ∈ Set.Icc 0 T,
      c t = (0 : EuclideanSpace ℝ (Fin m)) + ∫ s in (0 : ℝ)..t, rhs s := by
    simpa only [zero_add] using hcEq
  have hc0 : c 0 = 0 := by simpa using hcEq 0 ⟨le_rfl, hT.le⟩
  have henergy : ∀ t ∈ Set.Icc 0 T,
      y t + lam * (∫ s in (0 : ℝ)..t, z s) ≤
        energyGalerkinK lam D * (∫ s in (0 : ℝ)..t, y s) + ∫ s in (0 : ℝ)..t, q s := by
    intro t ht
    have hi := finitePrimitive_energy_identity hT hrhs hcPrim ⟨le_rfl, hT.le⟩ ht
    rw [hc0, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hi
    have hpair := finitePrimitive_energy_pairing_intervalIntegrable hT hrhs hcPrim
      ⟨le_rfl, hT.le⟩ ht
    have hyi : IntervalIntegrable y volume 0 t :=
      (hy.mono (Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hzi : IntervalIntegrable z volume 0 t :=
      (hz.mono (Set.Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
    have hqit : IntervalIntegrable q volume 0 t := hqi.mono_set
      (by simpa only [Set.uIcc_of_le hT.le, Set.uIcc_of_le ht.1] using
        (Set.Icc_subset_Icc le_rfl ht.2))
    have hp : (fun s => 2 * inner ℝ (rhs s) (c s) + lam * z s) ≤ᵐ[
        volume.restrict (Set.Ioo 0 t)] (fun s => energyGalerkinK lam D * y s + q s) := by
      have hg := hGard.filter_mono (ae_mono
        (Measure.restrict_mono (Set.Ioo_subset_Ioo le_rfl ht.2) le_rfl))
      filter_upwards [hg] with s hs
      exact energyGalerkin_pointwise_energy e (B s) (F s) (c s) (hs (R (c s)))
    have hInt := energy_intervalIntegral_mono_ae_open ht.1
      ((hpair.const_mul 2).add (hzi.const_mul lam))
      ((hyi.const_mul (energyGalerkinK lam D)).add hqit) hp
    rw [intervalIntegral.integral_add (hpair.const_mul 2) (hzi.const_mul lam),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hyi.const_mul (energyGalerkinK lam D)) hqit,
      intervalIntegral.integral_const_mul, ← hi, ← energyGalerkin_norm_sq e he (c t)] at hInt
    exact hInt
  have hbound := energy_scalar_uniform_bound hT hlam hy hz
    (fun _ _ => sq_nonneg _) (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    hqi (fun _ => sq_nonneg _) henergy
  simpa only [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo]
    using hbound

/-- The actual coefficient form on interior times, extended by zero elsewhere. -/
def energyGalerkinActualForm (O : Set (Space n))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (T A D : ℝ)
    (hBounds : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D) (t : ℝ) :
    EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ :=
  if ht : t ∈ Set.Ioo 0 T then energyForm (hBounds t ht) else 0

theorem energyGalerkinActualForm_apply {T A D : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hBounds : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (v w : EnergyGraphSpace O) :
    energyGalerkinActualForm O a b T A D hBounds t v w = energyFormValue O a b t v w := by
  simp only [energyGalerkinActualForm, dite_eq_left ht, energyForm_apply]

theorem energyGalerkinActualMatrix_apply {T A D : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hBounds : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D)
    (e : Fin m → EnergyGraphSpace O) {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (c : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    energyGalerkinMatrix e (energyGalerkinActualForm O a b T A D hBounds t) c i =
      ∑ j, energyFormValue O a b t (e j) (e i) * c j := by
  simp only [energyGalerkinMatrix_apply, energyGalerkinActualForm_apply hBounds ht]

theorem energyGalerkinActualForm_norm_bound {T A D : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hBounds : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
      ‖energyGalerkinActualForm O a b T A D hBounds t‖ ≤ energyFormBound n A D := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simp only [energyGalerkinActualForm, dite_eq_left ht]
  exact energyForm_norm_le (hBounds t ht)

theorem energyGalerkinActualForm_entries {T A D : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hBounds : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D)
    (e : Fin m → EnergyGraphSpace O)
    (hMeas : ∀ i j, AEStronglyMeasurable
      (fun t => energyFormValue O a b t (e j) (e i)) (volume.restrict (Set.Ioo 0 T))) :
    ∀ i j, AEStronglyMeasurable
      (fun t => energyGalerkinActualForm O a b T A D hBounds t (e j) (e i))
      (volume.restrict (Set.Ioo 0 T)) := by
  intro i j
  apply (hMeas i j).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (energyGalerkinActualForm_apply hBounds ht (e j) (e i)).symm

theorem energyGalerkinActualForm_garding {T A D lam upper : ℝ}
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {Q : Set (Point n)}
    (hBounds : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D)
    (hO : MeasurableSet O) (hEll : Elliptic Q a lam upper)
    (hSlice : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ O, (x,t) ∈ Q) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : EnergyGraphSpace O,
      lam * (∑ i, ‖energyGradientProjection O i v‖ ^ 2) -
        (D ^ 2 / lam) * ‖energyValueProjection O v‖ ^ 2 ≤
          2 * energyGalerkinActualForm O a b T A D hBounds t v v := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  intro v
  simp only [energyGalerkinActualForm, dite_eq_left ht]
  exact energyForm_garding_clm (hBounds t ht) hO hEll (hSlice t ht) v

/-- Genuine finite-dimensional projected evolution with rough `L²` forcing,
including dimension zero, together with the basis-independent energy estimate. -/
theorem energyGalerkin_exists_with_uniform_bound {T lam D M : ℝ}
    (hT : 0 < T) (hlam : 0 < lam) (hM : 0 ≤ M)
    (e : Fin m → EnergyGraphSpace O)
    (he : Orthonormal ℝ (fun i => energyValueProjection O (e i)))
    (B : ℝ → EnergyGraphSpace O →L[ℝ] EnergyGraphSpace O →L[ℝ] ℝ)
    (hEntries : ∀ i j, AEStronglyMeasurable (fun t => B t (e j) (e i))
      (volume.restrict (Set.Ioo 0 T)))
    (hAM : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ‖energyGalerkinMatrix e (B t)‖ ≤ M)
    (hGard : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ∀ v : EnergyGraphSpace O,
      lam * (∑ i, ‖energyGradientProjection O i v‖ ^ 2) -
        (D ^ 2 / lam) * ‖energyValueProjection O v‖ ^ 2 ≤ 2 * B t v v)
    {F : ℝ → Lp ℝ 2 (volume.restrict O)}
    (hF : MemLp F 2 (volume.restrict (Set.Ioo 0 T))) :
    ∃ c : ℝ → EuclideanSpace ℝ (Fin m),
      ContinuousOn c (Set.Icc 0 T) ∧ c 0 = 0 ∧
      (∀ t ∈ Set.Icc 0 T, c t = ∫ s in (0 : ℝ)..t,
        energyGalerkinForcing e (F s) - energyGalerkinMatrix e (B s) (c s)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), HasDerivAt c
        (energyGalerkinForcing e (F t) - energyGalerkinMatrix e (B t) (c t)) t) ∧
      (∀ t ∈ Set.Icc 0 T,
        ‖energyValueProjection O (energyGalerkinReconstruction e (c t))‖ ^ 2 ≤
          energyGalerkinE T lam D * (∫ s in Set.Ioo 0 T, ‖F s‖ ^ 2)) ∧
      (∫ s in Set.Ioo 0 T,
        ‖energyValueProjection O (energyGalerkinReconstruction e (c s))‖ ^ 2 +
          ∑ i, ‖energyGradientProjection O i (energyGalerkinReconstruction e (c s))‖ ^ 2) ≤
        energyGalerkinC T lam D * (∫ s in Set.Ioo 0 T, ‖F s‖ ^ 2) := by
  obtain ⟨c, hc, hc0, hcEq, hcDeriv⟩ := finiteVolterra_exists m hT hM
    (fun t => energyGalerkinMatrix e (B t)) (fun t => energyGalerkinForcing e (F t))
    (energyGalerkinMatrix_aestronglyMeasurable e B hEntries) hAM
    ((energyGalerkinForcing e).integrable_comp (hF.integrable (by norm_num)))
  obtain ⟨hpoint, hint⟩ := energyGalerkin_uniform_of_integralODE hT hlam
    e he B hEntries hAM hGard hF hc hcEq
  exact ⟨c, hc, hc0, hcEq, hcDeriv, hpoint, hint⟩

/-- The actual divergence-form coefficient matrix has finite projected solutions
and the explicit uniform graph-energy estimate. The inputs concern the actual
coefficient bounds and scalar form measurability; no PDE solver is an input. -/
theorem energyGalerkin_actual_exists_with_uniform_bound {T A D lam upper : ℝ}
    (hT : 0 < T) (hlam : 0 < lam) (hA : 0 ≤ A) (hD : 0 ≤ D)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {Q : Set (Point n)}
    (hBounds : ∀ t ∈ Set.Ioo 0 T, EnergySliceBounds O a b t A D)
    (hO : MeasurableSet O) (hEll : Elliptic Q a lam upper)
    (hSlice : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ O, (x,t) ∈ Q)
    (e : Fin m → EnergyGraphSpace O)
    (he : Orthonormal ℝ (fun i => energyValueProjection O (e i)))
    (hMeas : ∀ i j, AEStronglyMeasurable
      (fun t => energyFormValue O a b t (e j) (e i)) (volume.restrict (Set.Ioo 0 T)))
    {F : ℝ → Lp ℝ 2 (volume.restrict O)}
    (hF : MemLp F 2 (volume.restrict (Set.Ioo 0 T))) :
    ∃ c : ℝ → EuclideanSpace ℝ (Fin m),
      ContinuousOn c (Set.Icc 0 T) ∧ c 0 = 0 ∧
      (∀ t ∈ Set.Icc 0 T, c t = ∫ s in (0 : ℝ)..t,
        energyGalerkinForcing e (F s) -
          energyGalerkinMatrix e (energyGalerkinActualForm O a b T A D hBounds s) (c s)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), HasDerivAt c
        (energyGalerkinForcing e (F t) -
          energyGalerkinMatrix e (energyGalerkinActualForm O a b T A D hBounds t) (c t)) t) ∧
      (∀ t ∈ Set.Icc 0 T,
        ‖energyValueProjection O (energyGalerkinReconstruction e (c t))‖ ^ 2 ≤
          energyGalerkinE T lam D * (∫ s in Set.Ioo 0 T, ‖F s‖ ^ 2)) ∧
      (∫ s in Set.Ioo 0 T,
        ‖energyValueProjection O (energyGalerkinReconstruction e (c s))‖ ^ 2 +
          ∑ i, ‖energyGradientProjection O i (energyGalerkinReconstruction e (c s))‖ ^ 2) ≤
        energyGalerkinC T lam D * (∫ s in Set.Ioo 0 T, ‖F s‖ ^ 2) := by
  let B := energyGalerkinActualForm O a b T A D hBounds
  let M := ‖energyGalerkinTestEvaluation e‖ * energyFormBound n A D *
    ‖energyGalerkinReconstruction e‖
  have hEval : 0 ≤ ‖energyGalerkinTestEvaluation e‖ :=
    @ContinuousLinearMap.opNorm_nonneg ℝ ℝ (EnergyGraphSpace O →L[ℝ] ℝ)
      (EuclideanSpace ℝ (Fin m)) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) (energyGalerkinTestEvaluation e)
  have hRec : 0 ≤ ‖energyGalerkinReconstruction e‖ :=
    @ContinuousLinearMap.opNorm_nonneg ℝ ℝ (EuclideanSpace ℝ (Fin m))
      (EnergyGraphSpace O) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance (RingHom.id ℝ) (energyGalerkinReconstruction e)
  have hM : 0 ≤ M := mul_nonneg
    (mul_nonneg hEval (energyFormBound_pos hA hD).le) hRec
  have hAM : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), ‖energyGalerkinMatrix e (B t)‖ ≤ M := by
    filter_upwards [energyGalerkinActualForm_norm_bound hBounds] with t ht
    exact (energyGalerkinMatrix_norm_le e (B t)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hEval) hRec)
  exact energyGalerkin_exists_with_uniform_bound hT hlam hM e he B
    (energyGalerkinActualForm_entries hBounds e hMeas) hAM
    (energyGalerkinActualForm_garding hBounds hO hEll hSlice) hF

end Yau.LeafProofs.L16Aux
