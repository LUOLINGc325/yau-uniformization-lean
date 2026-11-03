import Yau.LeafProofs.L17UniformPartition
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The actual atlas Holder graph on the actual closed manifold-time cylinder. -/

open Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17HolderAux
open Yau.LeafProofs.L17Aux

abbrev Time (T : ℝ) := ↥(Icc (0 : ℝ) T)
abbrev Cylinder {n : ℕ} (M : ComplexManifold n) (T : ℝ) := M.Carrier × Time T

abbrev ChartCylinder {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
    (P : UniformChartPartition g) (T : ℝ) :=
  ↥(ball (0 : ComplexVector n) P.radius) × Time T

abbrev ChartPairs {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
    (P : UniformChartPartition g) (T : ℝ) :=
  Σ _ : P.centers, {q : ChartCylinder P T × ChartCylinder P T // q.1 ≠ q.2}

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def chartPoint (P : UniformChartPartition g) (T : ℝ) (p : P.centers)
    (q : ChartCylinder P T) : Cylinder M T := (P.charts.chart p q.1,q.2)

theorem chartPoint_continuous (P : UniformChartPartition g) (T : ℝ) (p : P.centers) :
    Continuous (chartPoint P T p) := by
  have hChart : Continuous (fun z : ↥(ball (0 : ComplexVector n) P.radius) => P.charts.chart p z) :=
    (P.charts.chart p).continuousOn.comp_continuous continuous_subtype_val (fun z =>
      P.charts.closedBall_source p (ball_subset_closedBall
        ((ball_subset_ball P.radius_lt.le) z.property)))
  exact (hChart.comp continuous_fst).prodMk continuous_snd

def chartLeft (P : UniformChartPartition g) (T : ℝ) (i : ChartPairs P T) : Cylinder M T :=
  chartPoint P T i.1 i.2.val.1

def chartRight (P : UniformChartPartition g) (T : ℝ) (i : ChartPairs P T) : Cylinder M T :=
  chartPoint P T i.1 i.2.val.2

theorem chartLeft_continuous (P : UniformChartPartition g) (T : ℝ) : Continuous (chartLeft P T) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact (chartPoint_continuous P T p).comp (continuous_fst.comp continuous_subtype_val)

theorem chartRight_continuous (P : UniformChartPartition g) (T : ℝ) : Continuous (chartRight P T) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact (chartPoint_continuous P T p).comp (continuous_snd.comp continuous_subtype_val)

def parabolicDistance {P : UniformChartPartition g} {T : ℝ}
    (q r : ChartCylinder P T) : ℝ :=
  ‖(q.1 : ComplexVector n)-(r.1 : ComplexVector n)‖+
    Real.sqrt |(q.2 : ℝ)-(r.2 : ℝ)|

theorem parabolicDistance_pos_of_ne {P : UniformChartPartition g} {T : ℝ}
    {q r : ChartCylinder P T} (hqr : q ≠ r) : 0 < parabolicDistance q r := by
  dsimp only [parabolicDistance]
  by_cases hz : (q.1 : ComplexVector n) = (r.1 : ComplexVector n)
  · have ht : (q.2 : ℝ) ≠ (r.2 : ℝ) := fun h => hqr (Prod.ext (Subtype.ext hz) (Subtype.ext h))
    exact add_pos_of_nonneg_of_pos (norm_nonneg _)
      (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr ht)))
  · exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr (sub_ne_zero.mpr hz)) (Real.sqrt_nonneg _)

theorem parabolicDistance_continuous (P : UniformChartPartition g) (T : ℝ) :
    Continuous (fun q : ChartCylinder P T × ChartCylinder P T => parabolicDistance q.1 q.2) := by
  have hx : Continuous (fun q : ChartCylinder P T => (q.1 : ComplexVector n)) :=
    continuous_subtype_val.comp continuous_fst
  have ht : Continuous (fun q : ChartCylinder P T => (q.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact ((hx.comp continuous_fst).sub (hx.comp continuous_snd)).norm.add
    (((ht.comp continuous_fst).sub (ht.comp continuous_snd)).abs.sqrt)

def scaledPairWeight (P : UniformChartPartition g) (γ : ℝ) {T : ℝ}
    (q r : ChartCylinder P T) : ℝ := P.radius^γ/(parabolicDistance q r)^γ

def pairWeight (P : UniformChartPartition g) (T γ : ℝ) (i : ChartPairs P T) : ℝ :=
  scaledPairWeight P γ i.2.val.1 i.2.val.2

theorem pairWeight_pos (P : UniformChartPartition g) (T γ : ℝ) (i : ChartPairs P T) :
    0 < pairWeight P T γ i :=
  div_pos (Real.rpow_pos_of_pos P.radius_pos γ)
    (Real.rpow_pos_of_pos (parabolicDistance_pos_of_ne i.2.property) γ)

theorem pairWeight_continuous (P : UniformChartPartition g) (T γ : ℝ) :
    Continuous (pairWeight P T γ) := by
  apply continuous_sigma_iff.mpr
  intro p
  have hD : Continuous (fun i : {q : ChartCylinder P T × ChartCylinder P T // q.1 ≠ q.2} =>
      parabolicDistance i.val.1 i.val.2) :=
    (parabolicDistance_continuous P T).comp continuous_subtype_val
  have hPow := hD.rpow_const (p := γ) (fun i => Or.inl (parabolicDistance_pos_of_ne i.property).ne')
  exact continuous_const.div hPow
    (fun i => (Real.rpow_pos_of_pos (parabolicDistance_pos_of_ne i.property) γ).ne')

abbrev HolderAmbient (P : UniformChartPartition g) (T : ℝ) :=
  BoundedContinuousFunction (Cylinder M T) ℝ × BoundedContinuousFunction (ChartPairs P T) ℝ

/-- The quotient is exactly the displayed scaled chart difference of the
same actual function, at every pair in every selected chart. -/
def HolderSpace (P : UniformChartPartition g) (T γ : ℝ) : Submodule ℝ (HolderAmbient P T) where
  carrier := {u | ∀ i : ChartPairs P T,
    u.2 i = pairWeight P T γ i*(u.1 (chartRight P T i)-u.1 (chartLeft P T i))}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro u v hu hv i
    change u.2 i+v.2 i = pairWeight P T γ i*
      ((u.1 (chartRight P T i)+v.1 (chartRight P T i))-(u.1 (chartLeft P T i)+v.1 (chartLeft P T i)))
    rw [hu i,hv i]
    ring
  smul_mem' := by
    intro c u hu i
    change c*u.2 i = pairWeight P T γ i*(c*u.1 (chartRight P T i)-c*u.1 (chartLeft P T i))
    rw [hu i]
    ring

theorem holderSpace_isClosed (P : UniformChartPartition g) (T γ : ℝ) :
    IsClosed (HolderSpace P T γ : Set (HolderAmbient P T)) := by
  change IsClosed {u : HolderAmbient P T | ∀ i : ChartPairs P T,
    u.2 i = pairWeight P T γ i*(u.1 (chartRight P T i)-u.1 (chartLeft P T i))}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_eq
    ((BoundedContinuousFunction.evalCLM ℝ i).continuous.comp continuous_snd)
    (continuous_const.mul
      (((BoundedContinuousFunction.evalCLM ℝ (chartRight P T i)).continuous.comp continuous_fst).sub
        ((BoundedContinuousFunction.evalCLM ℝ (chartLeft P T i)).continuous.comp continuous_fst)))

instance holderSpace_normedAddCommGroup (P : UniformChartPartition g) (T γ : ℝ) :
    NormedAddCommGroup (HolderSpace P T γ) := inferInstance

instance holderSpace_normedSpace (P : UniformChartPartition g) (T γ : ℝ) :
    NormedSpace ℝ (HolderSpace P T γ) := inferInstance

instance holderSpace_completeSpace (P : UniformChartPartition g) (T γ : ℝ) :
    CompleteSpace (HolderSpace P T γ) := (holderSpace_isClosed P T γ).completeSpace_coe

def valueCLM (P : UniformChartPartition g) (T γ : ℝ) :
    HolderSpace P T γ →L[ℝ] BoundedContinuousFunction (Cylinder M T) ℝ :=
  (ContinuousLinearMap.fst ℝ (BoundedContinuousFunction (Cylinder M T) ℝ)
    (BoundedContinuousFunction (ChartPairs P T) ℝ)).comp (HolderSpace P T γ).subtypeL

def holderFun {P : UniformChartPartition g} {T γ : ℝ} (u : HolderSpace P T γ) : Cylinder M T → ℝ :=
  u.val.1

theorem valueCLM_apply (P : UniformChartPartition g) (T γ : ℝ) (u : HolderSpace P T γ) :
    valueCLM P T γ u = u.val.1 := rfl

def quotientCLM (P : UniformChartPartition g) (T γ : ℝ) :
    HolderSpace P T γ →L[ℝ] BoundedContinuousFunction (ChartPairs P T) ℝ :=
  (ContinuousLinearMap.snd ℝ (BoundedContinuousFunction (Cylinder M T) ℝ)
    (BoundedContinuousFunction (ChartPairs P T) ℝ)).comp (HolderSpace P T γ).subtypeL

theorem quotientCLM_apply (P : UniformChartPartition g) (T γ : ℝ)
    (u : HolderSpace P T γ) (i : ChartPairs P T) :
    quotientCLM P T γ u i = pairWeight P T γ i*
      (holderFun u (chartRight P T i)-holderFun u (chartLeft P T i)) := u.property i

def evalCLM (P : UniformChartPartition g) (T γ : ℝ) (x : Cylinder M T) :
    HolderSpace P T γ →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ x).comp (valueCLM P T γ)

theorem evalCLM_apply (P : UniformChartPartition g) (T γ : ℝ)
    (x : Cylinder M T) (u : HolderSpace P T γ) : evalCLM P T γ x u = holderFun u x := rfl

theorem valueCLM_injective (P : UniformChartPartition g) (T γ : ℝ) :
    Function.Injective (valueCLM P T γ) := by
  intro u v huv
  have hValue : u.val.1 = v.val.1 := huv
  apply Subtype.ext
  apply Prod.ext hValue
  apply BoundedContinuousFunction.ext
  intro i
  rw [u.property i,v.property i,hValue]

theorem holderFun_injective (P : UniformChartPartition g) (T γ : ℝ) :
    Function.Injective (holderFun (P := P) (T := T) (γ := γ)) := by
  intro u v huv
  apply valueCLM_injective P T γ
  exact BoundedContinuousFunction.ext (fun x => congrFun huv x)

theorem norm_eq_max (P : UniformChartPartition g) (T γ : ℝ) (u : HolderSpace P T γ) :
    ‖u‖ = max ‖u.val.1‖ ‖u.val.2‖ := rfl

theorem norm_eq_max_projections (P : UniformChartPartition g) (T γ : ℝ)
    (u : HolderSpace P T γ) :
    ‖u‖ = max ‖valueCLM P T γ u‖ ‖quotientCLM P T γ u‖ := rfl

theorem valueCLM_opNorm_le_one (P : UniformChartPartition g) (T γ : ℝ) :
    ‖valueCLM P T γ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖u.val.1‖ ≤ 1*max ‖u.val.1‖ ‖u.val.2‖
  rw [one_mul]
  exact le_max_left _ _

theorem value_abs_le_norm {P : UniformChartPartition g} {T γ : ℝ}
    (u : HolderSpace P T γ) (x : Cylinder M T) : |holderFun u x| ≤ ‖u‖ := by
  change |u.val.1 x| ≤ max ‖u.val.1‖ ‖u.val.2‖
  have h := (u.val.1.norm_coe_le_norm x).trans (le_max_left ‖u.val.1‖ ‖u.val.2‖)
  simpa only [Real.norm_eq_abs] using h

theorem weighted_difference_abs_le_norm {P : UniformChartPartition g} {T γ : ℝ}
    (u : HolderSpace P T γ) (i : ChartPairs P T) :
    |pairWeight P T γ i*(holderFun u (chartRight P T i)-holderFun u (chartLeft P T i))| ≤ ‖u‖ := by
  change |pairWeight P T γ i*(u.val.1 (chartRight P T i)-u.val.1 (chartLeft P T i))| ≤
    max ‖u.val.1‖ ‖u.val.2‖
  have h := (u.val.2.norm_coe_le_norm i).trans (le_max_right ‖u.val.1‖ ‖u.val.2‖)
  rw [u.property i] at h
  simpa only [Real.norm_eq_abs] using h

theorem evalCLM_opNorm_le_one (P : UniformChartPartition g) (T γ : ℝ) (x : Cylinder M T) :
    ‖evalCLM P T γ x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖holderFun u x‖ ≤ 1*‖u‖
  simpa only [Real.norm_eq_abs,one_mul] using value_abs_le_norm u x

/-- The norm is exactly controlled by the two actual uniform scalar bounds,
without referring to an unproved supremum or abstract boundedness predicate. -/
theorem norm_le_iff {P : UniformChartPartition g} {T γ C : ℝ}
    (u : HolderSpace P T γ) (hC : 0 ≤ C) : ‖u‖ ≤ C ↔
    (∀ x, |holderFun u x| ≤ C) ∧
      ∀ i : ChartPairs P T,
        |pairWeight P T γ i*(holderFun u (chartRight P T i)-holderFun u (chartLeft P T i))| ≤ C := by
  constructor
  · intro h
    exact ⟨fun x => (value_abs_le_norm u x).trans h,
      fun i => (weighted_difference_abs_le_norm u i).trans h⟩
  · intro h
    rw [norm_eq_max]
    apply max_le
    · apply (BoundedContinuousFunction.norm_le hC).mpr
      intro x
      change ‖holderFun u x‖ ≤ C
      simpa only [Real.norm_eq_abs] using h.1 x
    · apply (BoundedContinuousFunction.norm_le hC).mpr
      intro i
      rw [u.property i]
      change ‖pairWeight P T γ i*(holderFun u (chartRight P T i)-holderFun u (chartLeft P T i))‖ ≤ C
      simpa only [Real.norm_eq_abs] using h.2 i

theorem norm_zero_iff_function_zero {P : UniformChartPartition g} {T γ : ℝ}
    (u : HolderSpace P T γ) : ‖u‖ = 0 ↔ ∀ x, holderFun u x = 0 := by
  constructor
  · intro h x
    have hu := norm_eq_zero.mp h
    subst u
    rfl
  · intro h
    have hu : u = 0 := holderFun_injective P T γ (funext h)
    rw [hu,norm_zero]

theorem weighted_difference_continuous (P : UniformChartPartition g) (T γ : ℝ)
    {f : Cylinder M T → ℝ} (hf : Continuous f) :
    Continuous (fun i : ChartPairs P T => pairWeight P T γ i*(f (chartRight P T i)-f (chartLeft P T i))) :=
  (pairWeight_continuous P T γ).mul ((hf.comp (chartRight_continuous P T)).sub
    (hf.comp (chartLeft_continuous P T)))

/-- A real bounded continuous function is constructed from actual scalar
bounds. Bounded-continuous-function membership is an output, not a premise. -/
def boundedContinuousOfAbsBound {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (A : ℝ) (hA : ∀ x, |f x| ≤ A) :
    BoundedContinuousFunction X ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f,hf⟩ (2*A) (by
    intro x y
    rw [dist_eq_norm,Real.norm_eq_abs]
    change |f x-f y| ≤ 2*A
    exact (abs_sub _ _).trans (by linarith [hA x,hA y]))

/-- The canonical actual Holder graph element from an actual continuous
function and its actual uniform value and scaled chart-difference bounds. -/
def ofBounds (P : UniformChartPartition g) (T γ : ℝ)
    (f : Cylinder M T → ℝ) (hf : Continuous f) (A B : ℝ)
    (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ i : ChartPairs P T,
      |pairWeight P T γ i*(f (chartRight P T i)-f (chartLeft P T i))| ≤ B) : HolderSpace P T γ :=
  ⟨(boundedContinuousOfAbsBound f hf A hA,
    boundedContinuousOfAbsBound _ (weighted_difference_continuous P T γ hf) B hB),by intro i; rfl⟩

theorem ofBounds_value (P : UniformChartPartition g) (T γ : ℝ)
    (f : Cylinder M T → ℝ) (hf : Continuous f) (A B : ℝ)
    (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ i : ChartPairs P T,
      |pairWeight P T γ i*(f (chartRight P T i)-f (chartLeft P T i))| ≤ B) :
    holderFun (ofBounds P T γ f hf A B hA hB) = f := rfl

theorem ofBounds_norm_le (P : UniformChartPartition g) (T γ : ℝ)
    (f : Cylinder M T → ℝ) (hf : Continuous f) (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ i : ChartPairs P T,
      |pairWeight P T γ i*(f (chartRight P T i)-f (chartLeft P T i))| ≤ B) :
    ‖ofBounds P T γ f hf A B hA hB‖ ≤ max A B := by
  change max ‖(ofBounds P T γ f hf A B hA hB).val.1‖ ‖(ofBounds P T γ f hf A B hA hB).val.2‖ ≤ _
  apply max_le
  · exact ((BoundedContinuousFunction.norm_le hA0).mpr (fun x => by
      change ‖f x‖ ≤ A
      simpa only [Real.norm_eq_abs] using hA x)).trans (le_max_left _ _)
  · exact ((BoundedContinuousFunction.norm_le hB0).mpr (fun i => by
      change ‖pairWeight P T γ i*(f (chartRight P T i)-f (chartLeft P T i))‖ ≤ B
      simpa only [Real.norm_eq_abs] using hB i)).trans (le_max_right _ _)

theorem exists_of_bounds (P : UniformChartPartition g) (T γ : ℝ)
    (f : Cylinder M T → ℝ) (hf : Continuous f) (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ x, |f x| ≤ A)
    (hB : ∀ i : ChartPairs P T,
      |pairWeight P T γ i*(f (chartRight P T i)-f (chartLeft P T i))| ≤ B) :
    ∃ u : HolderSpace P T γ, holderFun u = f ∧ ‖u‖ ≤ max A B :=
  ⟨ofBounds P T γ f hf A B hA hB,rfl,ofBounds_norm_le P T γ f hf A B hA0 hB0 hA hB⟩

end Yau.LeafProofs.L17HolderAux
