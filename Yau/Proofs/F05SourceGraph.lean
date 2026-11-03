import Yau.Proofs.F05AtlasModel
import Yau.LeafProofs.L16CompatibleHolderGraph

/-! Physical source functions form a closed finite product graph with exact overlaps. -/

open Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance source_componentGroup (α : ℝ) (Q : Set (Point n)) :
    NormedAddCommGroup (holderGraph α Q) := inferInstance
local instance source_componentSpace (α : ℝ) (Q : Set (Point n)) :
    NormedSpace ℝ (holderGraph α Q) := inferInstance

abbrev F05SourceAmbient (A : AtlasData M) (α T : ℝ) :=
  ∀ i : Fin A.count, holderGraph α (F05Q A i T)

def F05SourceCompatible (A : AtlasData M) (α T : ℝ) (f : F05SourceAmbient A α T) : Prop :=
  ∀ i j z w t, z ∈ F05D A i → w ∈ F05D A j → t ∈ Icc 0 T →
    lift A i z = lift A j w → holderGraphFun (f i) (z,t) = holderGraphFun (f j) (w,t)

def F05SourceInitialZero (A : AtlasData M) (α T : ℝ) (f : F05SourceAmbient A α T) : Prop :=
  ∀ i z, z ∈ F05D A i → holderGraphFun (f i) (z,0) = 0

def F05SourceGraph (A : AtlasData M) (α T : ℝ) : Submodule ℝ (F05SourceAmbient A α T) where
  carrier := {f | F05SourceCompatible A α T f}
  zero_mem' := by intro i j z w t hz hw ht heq; simp [holderGraphFun_zero]
  add_mem' := by
    intro f g hf hg i j z w t hz hw ht heq
    simp only [Pi.add_apply, holderGraphFun_add]
    rw [hf i j z w t hz hw ht heq, hg i j z w t hz hw ht heq]
  smul_mem' := by
    intro a f hf i j z w t hz hw ht heq
    simp only [Pi.smul_apply, holderGraphFun_smul, smul_eq_mul]
    rw [hf i j z w t hz hw ht heq]

def F05SourceZeroGraph (A : AtlasData M) (α T : ℝ) : Submodule ℝ (F05SourceAmbient A α T) where
  carrier := {f | F05SourceCompatible A α T f ∧ F05SourceInitialZero A α T f}
  zero_mem' := ⟨(F05SourceGraph A α T).zero_mem, by intro i z hz; simp [holderGraphFun_zero]⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨(F05SourceGraph A α T).add_mem hf.1 hg.1, ?_⟩
    intro i z hz
    simp only [Pi.add_apply, holderGraphFun_add, hf.2 i z hz, hg.2 i z hz, add_zero]
  smul_mem' := by
    intro a f hf
    refine ⟨(F05SourceGraph A α T).smul_mem a hf.1, ?_⟩
    intro i z hz
    simp only [Pi.smul_apply, holderGraphFun_smul, hf.2 i z hz, smul_zero]

instance F05_sourceGraph_normedAddCommGroup (A : AtlasData M) (α T : ℝ) :
    NormedAddCommGroup (F05SourceGraph A α T) := inferInstance
instance F05_sourceGraph_normedSpace (A : AtlasData M) (α T : ℝ) :
    NormedSpace ℝ (F05SourceGraph A α T) := inferInstance
instance F05_sourceZeroGraph_normedAddCommGroup (A : AtlasData M) (α T : ℝ) :
    NormedAddCommGroup (F05SourceZeroGraph A α T) := inferInstance
instance F05_sourceZeroGraph_normedSpace (A : AtlasData M) (α T : ℝ) :
    NormedSpace ℝ (F05SourceZeroGraph A α T) := inferInstance

theorem F05_sourceCompatible_isClosed (A : AtlasData M) (α T : ℝ) :
    IsClosed {f : F05SourceAmbient A α T | F05SourceCompatible A α T f} := by
  change IsClosed {f : F05SourceAmbient A α T | ∀ i j z w t,
    z ∈ F05D A i → w ∈ F05D A j → t ∈ Icc 0 T → lift A i z = lift A j w →
    holderGraphFun (f i) (z,t) = holderGraphFun (f j) (w,t)}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_iInter fun z => isClosed_iInter fun w => isClosed_iInter fun t =>
    isClosed_iInter fun hz => isClosed_iInter fun hw => isClosed_iInter fun ht =>
    isClosed_iInter fun heq => ?_
  exact isClosed_eq
    ((compatibleHolderGraph_eval_continuous (z,t)).comp (continuous_apply i))
    ((compatibleHolderGraph_eval_continuous (w,t)).comp (continuous_apply j))

theorem F05_sourceInitialZero_isClosed (A : AtlasData M) (α T : ℝ) :
    IsClosed {f : F05SourceAmbient A α T | F05SourceInitialZero A α T f} := by
  change IsClosed {f : F05SourceAmbient A α T | ∀ i z,
    z ∈ F05D A i → holderGraphFun (f i) (z,0) = 0}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun z => isClosed_iInter fun hz => ?_
  exact isClosed_eq ((compatibleHolderGraph_eval_continuous (z,0)).comp (continuous_apply i))
    continuous_const

theorem F05_sourceGraph_isClosed (A : AtlasData M) (α T : ℝ) :
    IsClosed (F05SourceGraph A α T : Set (F05SourceAmbient A α T)) :=
  F05_sourceCompatible_isClosed A α T

theorem F05_sourceZeroGraph_isClosed (A : AtlasData M) (α T : ℝ) :
    IsClosed (F05SourceZeroGraph A α T : Set (F05SourceAmbient A α T)) :=
  (F05_sourceCompatible_isClosed A α T).inter (F05_sourceInitialZero_isClosed A α T)

instance F05_sourceGraph_completeSpace (A : AtlasData M) (α T : ℝ) :
    CompleteSpace (F05SourceGraph A α T) := (F05_sourceGraph_isClosed A α T).completeSpace_coe

instance F05_sourceZeroGraph_completeSpace (A : AtlasData M) (α T : ℝ) :
    CompleteSpace (F05SourceZeroGraph A α T) := (F05_sourceZeroGraph_isClosed A α T).completeSpace_coe

def F05SourceFun {A : AtlasData M} {α T : ℝ} (f : F05SourceGraph A α T)
    (x : M.Carrier) (t : ℝ) : ℝ := by
  classical
  exact if t ∈ Icc 0 T then
    if H : ∃ i z, z ∈ F05D A i ∧ lift A i z = x then
      holderGraphFun (f.val H.choose) (H.choose_spec.choose,t)
    else 0
  else 0

theorem F05SourceFun_pull {A : AtlasData M} {α T : ℝ} (f : F05SourceGraph A α T)
    (i : Fin A.count) (z : Space n) (hz : z ∈ F05D A i) (t : ℝ) (ht : t ∈ Icc 0 T) :
    F05SourceFun f (lift A i z) t = holderGraphFun (f.val i) (z,t) := by
  classical
  have H : ∃ j w, w ∈ F05D A j ∧ lift A j w = lift A i z := ⟨i,z,hz,rfl⟩
  simp only [F05SourceFun, ite_eq_left ht, dite_eq_left H]
  exact f.property H.choose i H.choose_spec.choose z t H.choose_spec.choose_spec.1 hz ht
    H.choose_spec.choose_spec.2

theorem F05SourceFun_norm_le {A : AtlasData M} {α T : ℝ}
    (f : F05SourceGraph A α T) (x : M.Carrier) (t : ℝ) : |F05SourceFun f x t| ≤ ‖f‖ := by
  classical
  unfold F05SourceFun
  split_ifs with ht H
  · exact ((holderGraphFun_holderBound (f.val H.choose)).2.1
      (H.choose_spec.choose,t) ⟨H.choose_spec.choose_spec.1,ht⟩).trans
        (norm_le_pi_norm f.val H.choose)
  · simpa only [abs_zero] using norm_nonneg f
  · simpa only [abs_zero] using norm_nonneg f

theorem F05SourceFun_add {A : AtlasData M} {α T : ℝ} (f g : F05SourceGraph A α T)
    (x : M.Carrier) (t : ℝ) : F05SourceFun (f+g) x t = F05SourceFun f x t + F05SourceFun g x t := by
  classical
  unfold F05SourceFun
  split_ifs <;> simp [holderGraphFun_add]

theorem F05SourceFun_smul {A : AtlasData M} {α T : ℝ} (a : ℝ) (f : F05SourceGraph A α T)
    (x : M.Carrier) (t : ℝ) : F05SourceFun (a • f) x t = a * F05SourceFun f x t := by
  classical
  unfold F05SourceFun
  split_ifs <;> simp [holderGraphFun_smul]

theorem F05SourceGraph_value_ext {A : AtlasData M} {α T : ℝ}
    {f g : F05SourceGraph A α T} (hfg : ∀ x t, F05SourceFun f x t = F05SourceFun g x t) : f = g := by
  apply Subtype.ext
  funext i
  apply holderGraph_ext
  intro p
  have heq := hfg (lift A i p.val.1) p.val.2
  rw [F05SourceFun_pull f i p.val.1 p.property.1 p.val.2 p.property.2,
    F05SourceFun_pull g i p.val.1 p.property.1 p.val.2 p.property.2,
    holderGraphFun_apply _ p, holderGraphFun_apply _ p] at heq
  exact heq

end Yau.Proofs.F05Aux
