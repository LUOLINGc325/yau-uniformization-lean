import Yau.Proofs.F05SourceGraph

/-! Encoding actual scalar sources in the physical overlap graph. -/

open Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types true

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05SourceAmbientOfActual {A : AtlasData M} {α T F : ℝ} (hα : 0 < α)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F) :
    F05SourceAmbient A α T := fun i : Fin A.count =>
    @holderGraphOfBound n α F (F05Q A i T) (pull A i f) hα (hf i)

theorem F05SourceAmbientOfActual_eval {A : AtlasData M} {α T F : ℝ} (hα : 0 < α)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F)
    (i : Fin A.count) (p : Point n) (hp : p ∈ F05Q A i T) :
    holderGraphFun (F05SourceAmbientOfActual hα f hf i) p = pull A i f p :=
  holderGraphOfBound_eqOn hα (hf i) hp

theorem F05SourceAmbientOfActual_compatible {A : AtlasData M} {α T F : ℝ} (hα : 0 < α)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F) :
    F05SourceCompatible A α T (F05SourceAmbientOfActual hα f hf) := by
  intro i j z w t hz hw ht heq
  rw [F05SourceAmbientOfActual_eval hα f hf i (z,t) ⟨hz,ht⟩,
    F05SourceAmbientOfActual_eval hα f hf j (w,t) ⟨hw,ht⟩]
  exact congrArg (fun y => f y t) heq

def F05SourceOfActual {A : AtlasData M} {α T F : ℝ} (hα : 0 < α)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F) :
    F05SourceGraph A α T :=
  ⟨F05SourceAmbientOfActual hα f hf,F05SourceAmbientOfActual_compatible hα f hf⟩

theorem F05SourceOfActual_norm_le {A : AtlasData M} {α T F : ℝ} (hα : 0 < α)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F)
    (hF : 0 ≤ F) : ‖F05SourceOfActual hα f hf‖ ≤ F := by
  change ‖fun i : Fin A.count => holderGraphOfBound hα (hf i)‖ ≤ F
  exact (pi_norm_le_iff_of_nonneg hF).mpr fun i => holderGraphOfBound_norm_le hα (hf i)

theorem F05SourceOfActual_evaluation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {α T F : ℝ} (hα : 0 < α)
    (f : M.Carrier → ℝ → ℝ) (hf : ∀ i, HolderBound α (F05Q A i T) (pull A i f) F)
    (x : M.Carrier) (hx : x ∈ closure O) (t : ℝ) (ht : t ∈ Icc 0 T) :
    F05SourceFun (F05SourceOfActual hα f hf) x t = f x t := by
  obtain ⟨i,z,hz,rfl⟩ := F05_cover hA hx
  rw [F05SourceFun_pull _ i z hz t ht]
  exact holderGraphOfBound_eqOn hα (hf i) ⟨hz,ht⟩

end Yau.Proofs.F05Aux
