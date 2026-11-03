import Yau.Analysis.RangeRiesz
import Yau.LeafProofs.L03DivergenceEnergy
import Yau.LeafProofs.L03CompactGradientLimits

/-! Elementary weak differentiation for the finite-dimensional coordinate
spaces used by Hodge regularity. All tests and representatives are actual
functions, and no regularity conclusion is part of a definition. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

namespace Yau.NodeProofs.P06Aux

section TestFunctions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

/-- Actual smooth compact tests with support inside a prescribed region. -/
def regularityTest (O : Set E) (φ : E → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O

/-- Actual weak derivative tested against all compact smooth functions. -/
def regularityWeakDeriv (ν : Measure E) (O : Set E) (e : E)
    (u v : E → ℝ) : Prop :=
  ∀ φ : E → ℝ, regularityTest O φ →
    (∫ z, u z * fderiv ℝ φ z e ∂ν.restrict O) =
      -(∫ z, v z * φ z ∂ν.restrict O)

theorem regularityTest_direction {O : Set E} {φ : E → ℝ}
    (hφ : regularityTest O φ) (e : E) :
    regularityTest O (fun z => fderiv ℝ φ z e) :=
  ⟨((hφ.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const),
    hφ.2.1.fderiv_apply ℝ e, (tsupport_fderiv_apply_subset ℝ e).trans hφ.2.2⟩

theorem regularityTest_mul {O : Set E} {φ a : E → ℝ}
    (hφ : regularityTest O φ) (ha : ContDiff ℝ ∞ a) :
    regularityTest O (fun z => φ z * a z) :=
  ⟨hφ.1.mul ha, hφ.2.1.mul_right, tsupport_mul_subset_left.trans hφ.2.2⟩

def regularityTestSpace (O : Set E) : Submodule ℝ (E → ℝ) where
  carrier := {φ | regularityTest O φ}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro φ ψ hφ hψ
    exact ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
      (tsupport_add φ ψ).trans (Set.union_subset hφ.2.2 hψ.2.2)⟩
  smul_mem' := by
    intro c φ hφ
    exact ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ => c) φ).trans hφ.2.2⟩

variable (ν : Measure E) [IsLocallyFiniteMeasure ν]

theorem regularityTest_memLp {O : Set E} {φ : E → ℝ}
    (hφ : regularityTest O φ) : MemLp φ 2 (ν.restrict O) :=
  (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict O

def regularityTestToL2 (O : Set E) :
    regularityTestSpace O →ₗ[ℝ] Lp ℝ 2 (ν.restrict O) where
  toFun φ := (regularityTest_memLp ν φ.2).toLp φ.1
  map_add' φ ψ := MemLp.toLp_add (regularityTest_memLp ν φ.2)
    (regularityTest_memLp ν ψ.2)
  map_smul' c φ := MemLp.toLp_const_smul c (regularityTest_memLp ν φ.2)

def regularityTestDeriv (O : Set E) (e : E) :
    regularityTestSpace O →ₗ[ℝ] regularityTestSpace O where
  toFun φ := ⟨fun z => fderiv ℝ φ.1 z e, regularityTest_direction φ.2 e⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext z
    exact congrArg (fun L : E →L[ℝ] ℝ => L e)
      (fderiv_add (φ.2.1.differentiable (by simp) z)
        (ψ.2.1.differentiable (by simp) z))
  map_smul' c φ := by
    apply Subtype.ext
    funext z
    exact congrArg (fun L : E →L[ℝ] ℝ => L e)
      (fderiv_const_smul (φ.2.1.differentiable (by simp) z) c)

theorem inner_regularityTestToL2 {O : Set E}
    (g : Lp ℝ 2 (ν.restrict O)) (φ : regularityTestSpace O) :
    inner ℝ g (regularityTestToL2 ν O φ) =
      ∫ z, g z * φ.1 z ∂ν.restrict O := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(regularityTest_memLp ν φ.2).coeFn_toLp] with z hz
  simp only [regularityTestToL2, LinearMap.coe_mk, AddHom.coe_mk] at hz ⊢
  simp only [hz, RCLike.inner_apply, conj_trivial, mul_comm]

/-- A bounded distributional derivative has an actual L² representative,
with its original bound. This applies to finite coordinate space directly. -/
theorem regularityWeakDeriv_of_bound {O : Set E} (e : E) (u : E → ℝ)
    (hu : MemLp u 2 (ν.restrict O)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ : E → ℝ, regularityTest O φ →
      |∫ z, u z * fderiv ℝ φ z e ∂ν.restrict O| ≤
        C * (eLpNorm φ 2 (ν.restrict O)).toReal) :
    ∃ v : E → ℝ, MemLp v 2 (ν.restrict O) ∧
      eLpNorm v 2 (ν.restrict O) ≤ ENNReal.ofReal C ∧
      regularityWeakDeriv ν O e u v := by
  let L : regularityTestSpace O →ₗ[ℝ] ℝ :=
    -((innerSL ℝ (hu.toLp u)).toLinearMap.comp
      ((regularityTestToL2 ν O).comp (regularityTestDeriv O e)))
  have hL (φ : regularityTestSpace O) :
      L φ = -(∫ z, u z * fderiv ℝ φ.1 z e ∂ν.restrict O) := by
    change -inner ℝ (hu.toLp u)
      (regularityTestToL2 ν O (regularityTestDeriv O e φ)) = _
    rw [inner_regularityTestToL2]
    congr 1
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with z hz
    simp only [regularityTestDeriv, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hz]
  have hnorm (φ : regularityTestSpace O) :
      ‖L φ‖ ≤ C * ‖regularityTestToL2 ν O φ‖ := by
    rw [hL, norm_neg, Real.norm_eq_abs]
    change _ ≤ C * ‖(regularityTest_memLp ν φ.2).toLp φ.1‖
    rw [Lp.norm_toLp]
    exact hbound φ.1 φ.2
  obtain ⟨v, hv, htest⟩ := Yau.Analysis.exists_norm_le_inner_eq_of_range_bound
    (regularityTestToL2 ν O) L C hC hnorm
  refine ⟨v, Lp.memLp v, ?_, ?_⟩
  · exact (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top v)).symm ▸
      ENNReal.ofReal_le_ofReal hv
  · intro φ hφ
    have h := htest ⟨φ, hφ⟩
    rw [inner_regularityTestToL2, hL] at h
    linarith

theorem regularityTest_integral_restrict {O : Set E} {φ : E → ℝ}
    (hφ : regularityTest O φ) (u : E → ℝ) :
    (∫ z, u z * φ z ∂ν.restrict O) = ∫ z, u z * φ z ∂ν := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφ.2.2 h)), mul_zero]

theorem regularityWeakDeriv_mono {O V : Set E} {e : E} {u v : E → ℝ}
    (h : regularityWeakDeriv ν O e u v) (hVO : V ⊆ O) :
    regularityWeakDeriv ν V e u v := by
  intro φ hφ
  have hφO : regularityTest O φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVO⟩
  have hh := h φ hφO
  rw [regularityTest_integral_restrict ν (regularityTest_direction hφO e) u,
    regularityTest_integral_restrict ν hφO v] at hh
  rw [regularityTest_integral_restrict ν (regularityTest_direction hφ e) u,
    regularityTest_integral_restrict ν hφ v]
  exact hh

end TestFunctions

section StrongLimits
variable {E : Type*} [MeasurableSpace E] (ν : Measure E)

theorem regularityToLp_inner (u v : E → ℝ) (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    inner ℝ (hu.toLp u) (hv.toLp v) = ∫ z, u z * v z ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with z hzu hzv
  simp only [hzu, hzv, RCLike.inner_apply, conj_trivial, mul_comm]

theorem regularityToLp_norm_sq (u : E → ℝ) (hu : MemLp u 2 ν) :
    ‖hu.toLp u‖ ^ 2 = ∫ z, (u z) ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, regularityToLp_inner]
  simp only [pow_two]

/-- The raw squared-integral convergence used by the compact energy lemmas
is genuine strong convergence in L². -/
theorem regularityToLp_tendsto (u : ℕ → E → ℝ) (v : E → ℝ)
    (hu : ∀ m, MemLp (u m) 2 ν) (hv : MemLp v 2 ν)
    (ht : Tendsto (fun m => ∫ z, ‖u m z - v z‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun m => (hu m).toLp (u m)) atTop (𝓝 (hv.toLp v)) := by
  have hnorm (m : ℕ) :
      ‖(hu m).toLp (u m) - hv.toLp v‖ ^ 2 = ∫ z, ‖u m z - v z‖ ^ 2 ∂ν := by
    rw [← MemLp.toLp_sub (hu m) hv, regularityToLp_norm_sq]
    simp only [Pi.sub_apply, Real.norm_eq_abs, sq_abs]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp ht
  simpa only [← hnorm, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, Function.comp_def] using hs

theorem regularity_integral_pairing_tendsto (u : ℕ → E → ℝ) (v φ : E → ℝ)
    (hu : ∀ m, MemLp (u m) 2 ν) (hv : MemLp v 2 ν) (hφ : MemLp φ 2 ν)
    (ht : Tendsto (fun m => ∫ z, ‖u m z - v z‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ z, u m z * φ z ∂ν) atTop (𝓝 (∫ z, v z * φ z ∂ν)) := by
  have h : Tendsto (fun m => inner ℝ ((hu m).toLp (u m)) (hφ.toLp φ)) atTop
      (𝓝 (inner ℝ (hv.toLp v) (hφ.toLp φ))) :=
    (regularityToLp_tendsto ν u v hu hv ht).inner tendsto_const_nhds
  simpa only [regularityToLp_inner] using h

end StrongLimits

section WeakGradientLimits
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [ν.IsAddHaarMeasure]

/-- Strong L² convergence of smooth values and their true derivatives
produces a genuine weak derivative of the raw value limit. -/
theorem regularityWeakDeriv_of_smooth_limits (e : E) (U : ℕ → E → ℝ)
    (u v : E → ℝ) (hU : ∀ m, ContDiff ℝ ∞ (U m))
    (hcU : ∀ m, HasCompactSupport (U m))
    (hu : MemLp u 2 ν) (hv : MemLp v 2 ν)
    (hval : Tendsto (fun m => ∫ z, ‖U m z - u z‖ ^ 2 ∂ν) atTop (𝓝 0))
    (hder : Tendsto (fun m => ∫ z, ‖fderiv ℝ (U m) z e - v z‖ ^ 2 ∂ν)
      atTop (𝓝 0)) : regularityWeakDeriv ν Set.univ e u v := by
  intro φ hφ
  have hUL (m : ℕ) : MemLp (U m) 2 ν :=
    (hU m).continuous.memLp_of_hasCompactSupport (hcU m)
  have hDL (m : ℕ) : MemLp (fun z => fderiv ℝ (U m) z e) 2 ν :=
    (((hU m).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport ((hcU m).fderiv_apply ℝ e)
  have hφL : MemLp φ 2 ν := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
  have hDφL : MemLp (fun z => fderiv ℝ φ z e) 2 ν :=
    ((regularityTest_direction hφ e).1.continuous.memLp_of_hasCompactSupport
      (regularityTest_direction hφ e).2.1)
  have hleft := regularity_integral_pairing_tendsto ν U u
    (fun z => fderiv ℝ φ z e) hUL hu hDφL hval
  have hright := (regularity_integral_pairing_tendsto ν
    (fun m z => fderiv ℝ (U m) z e) v φ hDL hv hφL hder).neg
  have hIBP (m : ℕ) := Yau.LeafProofs.L03.DivergenceEnergy.compact_ibp
    ν (U m) φ (hU m) (hcU m) hφ.1 e
  simpa only [Measure.restrict_univ] using
    tendsto_nhds_unique hleft (hright.congr' (Eventually.of_forall fun m => (hIBP m).symm))

end WeakGradientLimits

abbrev HodgeCoordSpace (d : ℕ) := Fin d → ℝ

def HodgeCoordinateWeakJet {d : ℕ} {α : Type*} [Fintype α]
    (s : ℕ) (O : Set (HodgeCoordSpace d)) (u : HodgeCoordSpace d → α → ℝ)
    (J : List (Fin d) → HodgeCoordSpace d → α → ℝ) : Prop :=
  J [] = u ∧
  (∀ v, v.length ≤ s → ∀ c, MemLp (fun z => J v z c) 2 (volume.restrict O)) ∧
  ∀ v, v.length < s → ∀ i c,
    regularityWeakDeriv volume O (Pi.single i 1) (fun z => J v z c)
      (fun z => J (i :: v) z c)

end Yau.NodeProofs.P06Aux
