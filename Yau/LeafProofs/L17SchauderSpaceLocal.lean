import Yau.LeafProofs.L17HolderSpace
import Mathlib.Analysis.Normed.Operator.Prod

open Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

abbrev LocalCylinder (P : UniformChartPartition g) (T : ℝ) :=
  Σ _ : P.centers, ChartCylinder P T

def localLeft (P : UniformChartPartition g) (T : ℝ) (i : ChartPairs P T) : LocalCylinder P T :=
  ⟨i.1,i.2.val.1⟩
def localRight (P : UniformChartPartition g) (T : ℝ) (i : ChartPairs P T) : LocalCylinder P T :=
  ⟨i.1,i.2.val.2⟩

theorem localLeft_continuous (P : UniformChartPartition g) (T : ℝ) : Continuous (localLeft P T) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact continuous_sigmaMk.comp (continuous_fst.comp continuous_subtype_val)

theorem localRight_continuous (P : UniformChartPartition g) (T : ℝ) : Continuous (localRight P T) := by
  apply continuous_sigma_iff.mpr
  intro p
  exact continuous_sigmaMk.comp (continuous_snd.comp continuous_subtype_val)

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev LocalHolderAmbient (P : UniformChartPartition g) (T : ℝ) :=
  BoundedContinuousFunction (LocalCylinder P T) F × BoundedContinuousFunction (ChartPairs P T) F

def LocalHolderSpace (P : UniformChartPartition g) (T gamma : ℝ) :
    Submodule ℝ (LocalHolderAmbient F P T) where
  carrier := {u | ∀ i : ChartPairs P T,
    u.2 i = pairWeight P T gamma i • (u.1 (localRight P T i)-u.1 (localLeft P T i))}
  zero_mem' := by intro i; simp
  add_mem' := by
    intro u v hu hv i
    change u.2 i+v.2 i = pairWeight P T gamma i •
      ((u.1 (localRight P T i)+v.1 (localRight P T i))-
        (u.1 (localLeft P T i)+v.1 (localLeft P T i)))
    rw [hu i,hv i]
    simp only [smul_sub,smul_add]
    abel
  smul_mem' := by
    intro c u hu i
    change c • u.2 i = pairWeight P T gamma i •
      (c • u.1 (localRight P T i)-c • u.1 (localLeft P T i))
    rw [hu i,← smul_sub]
    exact smul_comm _ _ _

theorem localHolderSpace_isClosed (P : UniformChartPartition g) (T gamma : ℝ) :
    IsClosed (LocalHolderSpace F P T gamma : Set (LocalHolderAmbient F P T)) := by
  change IsClosed {u : LocalHolderAmbient F P T | ∀ i : ChartPairs P T,
    u.2 i = pairWeight P T gamma i • (u.1 (localRight P T i)-u.1 (localLeft P T i))}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_eq ((BoundedContinuousFunction.evalCLM ℝ i).continuous.comp continuous_snd)
    (continuous_const.smul
      (((BoundedContinuousFunction.evalCLM ℝ (localRight P T i)).continuous.comp continuous_fst).sub
        ((BoundedContinuousFunction.evalCLM ℝ (localLeft P T i)).continuous.comp continuous_fst)))

instance localHolderSpace_normedAddCommGroup (P : UniformChartPartition g) (T gamma : ℝ) :
    NormedAddCommGroup (LocalHolderSpace F P T gamma) := inferInstance
instance localHolderSpace_normedSpace (P : UniformChartPartition g) (T gamma : ℝ) :
    NormedSpace ℝ (LocalHolderSpace F P T gamma) := inferInstance
instance localHolderSpace_completeSpace [CompleteSpace F] (P : UniformChartPartition g) (T gamma : ℝ) :
    CompleteSpace (LocalHolderSpace F P T gamma) := (localHolderSpace_isClosed F P T gamma).completeSpace_coe

def localValueCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    LocalHolderSpace F P T gamma →L[ℝ] BoundedContinuousFunction (LocalCylinder P T) F :=
  (ContinuousLinearMap.fst ℝ (BoundedContinuousFunction (LocalCylinder P T) F)
    (BoundedContinuousFunction (ChartPairs P T) F)).comp (LocalHolderSpace F P T gamma).subtypeL

def localQuotientCLM (P : UniformChartPartition g) (T gamma : ℝ) :
    LocalHolderSpace F P T gamma →L[ℝ] BoundedContinuousFunction (ChartPairs P T) F :=
  (ContinuousLinearMap.snd ℝ (BoundedContinuousFunction (LocalCylinder P T) F)
    (BoundedContinuousFunction (ChartPairs P T) F)).comp (LocalHolderSpace F P T gamma).subtypeL

def localFun {P : UniformChartPartition g} {T gamma : ℝ}
    (u : LocalHolderSpace F P T gamma) : LocalCylinder P T → F := u.val.1

theorem localValueCLM_apply (P : UniformChartPartition g) (T gamma : ℝ)
    (u : LocalHolderSpace F P T gamma) : localValueCLM F P T gamma u = u.val.1 := rfl

theorem localQuotientCLM_apply (P : UniformChartPartition g) (T gamma : ℝ)
    (u : LocalHolderSpace F P T gamma) (i : ChartPairs P T) :
    localQuotientCLM F P T gamma u i = pairWeight P T gamma i •
      (localFun F u (localRight P T i)-localFun F u (localLeft P T i)) := u.property i

def localEvalCLM (P : UniformChartPartition g) (T gamma : ℝ) (q : LocalCylinder P T) :
    LocalHolderSpace F P T gamma →L[ℝ] F :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (localValueCLM F P T gamma)

theorem localFun_injective (P : UniformChartPartition g) (T gamma : ℝ) :
    Function.Injective (localFun F (P := P) (T := T) (gamma := gamma)) := by
  intro u v huv
  have hval : u.val.1 = v.val.1 := BoundedContinuousFunction.ext (fun q => congrFun huv q)
  apply Subtype.ext
  apply Prod.ext hval
  apply BoundedContinuousFunction.ext
  intro i
  rw [u.property i,v.property i,hval]

theorem localNorm_eq_max (P : UniformChartPartition g) (T gamma : ℝ)
    (u : LocalHolderSpace F P T gamma) :
    ‖u‖ = max ‖localValueCLM F P T gamma u‖ ‖localQuotientCLM F P T gamma u‖ := rfl

theorem localValue_norm_le {P : UniformChartPartition g} {T gamma : ℝ}
    (u : LocalHolderSpace F P T gamma) (q : LocalCylinder P T) : ‖localFun F u q‖ ≤ ‖u‖ :=
  (u.val.1.norm_coe_le_norm q).trans (le_max_left _ _)

theorem localWeighted_difference_norm_le {P : UniformChartPartition g} {T gamma : ℝ}
    (u : LocalHolderSpace F P T gamma) (i : ChartPairs P T) :
    ‖pairWeight P T gamma i • (localFun F u (localRight P T i)-localFun F u (localLeft P T i))‖ ≤ ‖u‖ := by
  rw [← localQuotientCLM_apply F P T gamma u i]
  exact (u.val.2.norm_coe_le_norm i).trans (le_max_right _ _)

theorem localValueCLM_opNorm_le_one (P : UniformChartPartition g) (T gamma : ℝ) :
    ‖localValueCLM F P T gamma‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖u.val.1‖ ≤ 1*max ‖u.val.1‖ ‖u.val.2‖
  simpa only [one_mul] using le_max_left ‖u.val.1‖ ‖u.val.2‖

theorem localEvalCLM_opNorm_le_one (P : UniformChartPartition g) (T gamma : ℝ) (q : LocalCylinder P T) :
    ‖localEvalCLM F P T gamma q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖localFun F u q‖ ≤ 1*‖u‖
  simpa only [one_mul] using localValue_norm_le F u q

theorem localNorm_le_iff {P : UniformChartPartition g} {T gamma C : ℝ}
    (u : LocalHolderSpace F P T gamma) (hC : 0 ≤ C) : ‖u‖ ≤ C ↔
    (∀ q, ‖localFun F u q‖ ≤ C) ∧ ∀ i : ChartPairs P T,
      ‖pairWeight P T gamma i • (localFun F u (localRight P T i)-localFun F u (localLeft P T i))‖ ≤ C := by
  constructor
  · intro h
    exact ⟨fun q => (localValue_norm_le F u q).trans h,fun i => (localWeighted_difference_norm_le F u i).trans h⟩
  · intro h
    change max ‖u.val.1‖ ‖u.val.2‖ ≤ C
    apply max_le
    · exact (BoundedContinuousFunction.norm_le hC).mpr h.1
    · apply (BoundedContinuousFunction.norm_le hC).mpr
      intro i
      rw [u.property i]
      exact h.2 i

theorem localWeighted_difference_continuous (P : UniformChartPartition g) (T gamma : ℝ)
    {f : LocalCylinder P T → F} (hf : Continuous f) :
    Continuous (fun i : ChartPairs P T => pairWeight P T gamma i •
      (f (localRight P T i)-f (localLeft P T i))) :=
  (pairWeight_continuous P T gamma).smul
    ((hf.comp (localRight_continuous P T)).sub (hf.comp (localLeft_continuous P T)))

def boundedContinuousOfNormBound {X : Type*} [TopologicalSpace X]
    (f : X → F) (hf : Continuous f) (A : ℝ) (hA : ∀ x, ‖f x‖ ≤ A) : BoundedContinuousFunction X F :=
  BoundedContinuousFunction.mkOfBound ⟨f,hf⟩ (2*A) (by
    intro x y
    rw [dist_eq_norm]
    change ‖f x-f y‖ ≤ 2*A
    exact (norm_sub_le (f x) (f y)).trans (by linarith only [hA x,hA y]))

def localOfBounds (P : UniformChartPartition g) (T gamma : ℝ)
    (f : LocalCylinder P T → F) (hf : Continuous f) (A B : ℝ)
    (hA : ∀ q, ‖f q‖ ≤ A)
    (hB : ∀ i : ChartPairs P T,
      ‖pairWeight P T gamma i • (f (localRight P T i)-f (localLeft P T i))‖ ≤ B) :
    LocalHolderSpace F P T gamma :=
  ⟨(boundedContinuousOfNormBound F f hf A hA,
    boundedContinuousOfNormBound F _ (localWeighted_difference_continuous F P T gamma hf) B hB),by intro i; rfl⟩

theorem localOfBounds_value (P : UniformChartPartition g) (T gamma : ℝ)
    (f : LocalCylinder P T → F) (hf : Continuous f) (A B : ℝ)
    (hA : ∀ q, ‖f q‖ ≤ A)
    (hB : ∀ i : ChartPairs P T,
      ‖pairWeight P T gamma i • (f (localRight P T i)-f (localLeft P T i))‖ ≤ B) :
    localFun F (localOfBounds F P T gamma f hf A B hA hB) = f := rfl

theorem localOfBounds_norm_le (P : UniformChartPartition g) (T gamma : ℝ)
    (f : LocalCylinder P T → F) (hf : Continuous f) (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ q, ‖f q‖ ≤ A)
    (hB : ∀ i : ChartPairs P T,
      ‖pairWeight P T gamma i • (f (localRight P T i)-f (localLeft P T i))‖ ≤ B) :
    ‖localOfBounds F P T gamma f hf A B hA hB‖ ≤ max A B := by
  change max ‖(localOfBounds F P T gamma f hf A B hA hB).val.1‖
    ‖(localOfBounds F P T gamma f hf A B hA hB).val.2‖ ≤ max A B
  apply max_le
  · exact ((BoundedContinuousFunction.norm_le hA0).mpr hA).trans (le_max_left _ _)
  · exact ((BoundedContinuousFunction.norm_le hB0).mpr hB).trans (le_max_right _ _)

end Yau.LeafProofs.L17SchauderAux
