import Yau.Proofs.F05SourceEncoding

/-! The all-initial-zero source graph evaluates to the same physical scalar functions. -/

open Set
open scoped Topology
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05SourceZeroInclusion (A : AtlasData M) (α T : ℝ) :
    F05SourceZeroGraph A α T →L[ℝ] F05SourceGraph A α T :=
  ({ toFun := fun f => ⟨f.val,f.property.1⟩
     map_add' := by intro f g; rfl
     map_smul' := by intro a f; rfl } :
    F05SourceZeroGraph A α T →ₗ[ℝ] F05SourceGraph A α T).mkContinuous 1 (by
      intro f
      simp only [one_mul]
      exact le_rfl)

def F05SourceZeroFun {A : AtlasData M} {α T : ℝ} (f : F05SourceZeroGraph A α T) :
    M.Carrier → ℝ → ℝ := F05SourceFun (F05SourceZeroInclusion A α T f)

theorem F05SourceZeroFun_pull {A : AtlasData M} {α T : ℝ} (f : F05SourceZeroGraph A α T)
    (i : Fin A.count) (z : Space n) (hz : z ∈ F05D A i) (t : ℝ) (ht : t ∈ Icc 0 T) :
    F05SourceZeroFun f (lift A i z) t = holderGraphFun (f.val i) (z,t) :=
  F05SourceFun_pull (F05SourceZeroInclusion A α T f) i z hz t ht

theorem F05SourceZeroFun_norm_le {A : AtlasData M} {α T : ℝ}
    (f : F05SourceZeroGraph A α T) (x : M.Carrier) (t : ℝ) : |F05SourceZeroFun f x t| ≤ ‖f‖ :=
  F05SourceFun_norm_le (F05SourceZeroInclusion A α T f) x t

theorem F05SourceZeroFun_initial {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α T : ℝ} (hT : 0 ≤ T) (f : F05SourceZeroGraph A α T)
    (x : M.Carrier) (hx : x ∈ closure O) : F05SourceZeroFun f x 0 = 0 := by
  obtain ⟨i,z,hz,rfl⟩ := F05_cover hA hx
  rw [F05SourceZeroFun_pull f i z hz 0 ⟨le_rfl,hT⟩]
  exact f.property.2 i z hz

theorem F05SourceZeroFun_add {A : AtlasData M} {α T : ℝ}
    (f g : F05SourceZeroGraph A α T) (x : M.Carrier) (t : ℝ) :
    F05SourceZeroFun (f+g) x t = F05SourceZeroFun f x t + F05SourceZeroFun g x t := by
  change F05SourceFun (F05SourceZeroInclusion A α T (f+g)) x t = _
  rw [map_add, F05SourceFun_add]
  rfl

theorem F05SourceZeroFun_smul {A : AtlasData M} {α T : ℝ}
    (a : ℝ) (f : F05SourceZeroGraph A α T) (x : M.Carrier) (t : ℝ) :
    F05SourceZeroFun (a • f) x t = a * F05SourceZeroFun f x t := by
  change F05SourceFun (F05SourceZeroInclusion A α T (a • f)) x t = _
  rw [map_smul, F05SourceFun_smul]
  rfl

def F05SourceZeroOfActual {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    {α T F : ℝ} (hT : 0 ≤ T) (hα : 0 < α) (f : M.Carrier → ℝ → ℝ)
    (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F)
    (hzero : ∀ x ∈ closure O, f x 0 = 0) : F05SourceZeroGraph A α T :=
  ⟨F05SourceAmbientOfActual hα f hf, F05SourceAmbientOfActual_compatible hα f hf, by
    intro i z hz
    rw [F05SourceAmbientOfActual_eval hα f hf i (z,0) ⟨hz,le_rfl,hT⟩]
    exact hzero _ (F05D_lift_mem_closure hA hz)⟩

theorem F05SourceZeroOfActual_norm_le {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α T F : ℝ} (hT : 0 ≤ T) (hα : 0 < α)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F)
    (hzero : ∀ x ∈ closure O, f x 0 = 0) (hF : 0 ≤ F) :
    ‖F05SourceZeroOfActual hA hT hα f hf hzero‖ ≤ F := by
  change ‖F05SourceOfActual hα f hf‖ ≤ F
  exact F05SourceOfActual_norm_le hα f hf hF

theorem F05SourceZeroOfActual_evaluation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α T F : ℝ} (hT : 0 ≤ T) (hα : 0 < α)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F)
    (hzero : ∀ x ∈ closure O, f x 0 = 0)
    (x : M.Carrier) (hx : x ∈ closure O) (t : ℝ) (ht : t ∈ Icc 0 T) :
    F05SourceZeroFun (F05SourceZeroOfActual hA hT hα f hf hzero) x t = f x t := by
  obtain ⟨i,z,hz,rfl⟩ := F05_cover hA hx
  rw [F05SourceZeroFun_pull _ i z hz t ht]
  exact F05SourceAmbientOfActual_eval hα f hf i (z,t) ⟨hz,ht⟩

end Yau.Proofs.F05Aux
