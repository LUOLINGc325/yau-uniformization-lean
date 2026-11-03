import Yau.Proofs.F05BoundaryCharts
import Yau.Proofs.F05FlatFactories

/-! The radius-two source region has the actual full-space or halfspace closure. -/

open Set
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05FlatOpen_closure (ν : Option (RIdx n)) :
    closure (F05FlatOpen ν) = {z : Space n | match ν with
      | none => True | some j => realCoord z j ≤ 0} := by
  cases ν with
  | none => simp [F05FlatOpen]
  | some j => exact coordinate_halfSpace_closure j

theorem F05ModelOpen_eq (A : AtlasData M) (i : Fin A.count) :
    F05ModelOpen A i = F05FlatOpen (A.normal i) := rfl

theorem F05D_subset_model_closure (A : AtlasData M) (i : Fin A.count) :
    F05D A i ⊆ closure (F05ModelOpen A i) := by
  intro z hz
  rw [F05ModelOpen_eq, F05FlatOpen_closure]
  exact hz.2

theorem F05Q_subset_model_cylinder (A : AtlasData M) (i : Fin A.count) (T : ℝ) :
    F05Q A i T ⊆ cylinder (closure (F05ModelOpen A i)) 0 T := by
  intro p hp
  exact ⟨F05D_subset_model_closure A i hp.1,hp.2⟩

theorem F05_source_cutoff_zero_outside (A : AtlasData M) (i : Fin A.count) (T : ℝ)
    (p : Point n) (hp : p ∈ cylinder (closure (F05ModelOpen A i)) 0 T)
    (hout : p ∉ F05Q A i T) : outerPatchBump 1 zero_lt_one (0 : Space n) p.1 = 0 := by
  by_contra hne
  have hn := outerPatchBump_nonzero_norm_lt zero_lt_one hne
  rw [sub_zero, mul_one] at hn
  have hh := hp.1
  rw [F05ModelOpen_eq, F05FlatOpen_closure] at hh
  exact hout ⟨⟨hn.le,hh⟩,hp.2⟩

end Yau.Proofs.F05Aux
