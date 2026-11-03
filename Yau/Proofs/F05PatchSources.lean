import Yau.Proofs.F05SourceZero
import Yau.Proofs.F05FlatRegions
import Yau.LeafProofs.L16HolderExtension

/-! A genuine cutoff extends each finite-chart source to the full physical model
as a bounded linear map, preserving the entire zero initial slice. -/

open Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1500000

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05PatchSource {A : AtlasData M} {α T : ℝ} (i : Fin A.count)
    (f : F05SourceZeroGraph A α T) (p : Point n) : ℝ :=
  outerPatchBump 1 zero_lt_one (0 : Space n) p.1 * holderGraphFun (f.val i) p

theorem F05PatchSource_add {A : AtlasData M} {α T : ℝ} (i : Fin A.count)
    (f g : F05SourceZeroGraph A α T) (p : Point n) :
    F05PatchSource i (f+g) p = F05PatchSource i f p + F05PatchSource i g p := by
  simp [F05PatchSource,holderGraphFun_add,mul_add]

theorem F05PatchSource_smul {A : AtlasData M} {α T : ℝ} (i : Fin A.count)
    (a : ℝ) (f : F05SourceZeroGraph A α T) (p : Point n) :
    F05PatchSource i (a • f) p = a * F05PatchSource i f p := by
  simp only [F05PatchSource,Submodule.coe_smul,Pi.smul_apply,holderGraphFun_smul,smul_eq_mul]
  ring

theorem F05PatchSource_initial {A : AtlasData M} {α T : ℝ} (i : Fin A.count)
    (f : F05SourceZeroGraph A α T) (x : Space n) : F05PatchSource i f (x,0) = 0 := by
  classical
  unfold F05PatchSource
  by_cases hx : x ∈ F05D A i
  · rw [f.property.2 i x hx,mul_zero]
  · have hp : (x,(0 : ℝ)) ∉ F05Q A i T := fun h => hx h.1
    simp only [holderGraphFun,dite_eq_right hp,mul_zero]

theorem F05PatchSource_holderBound {A : AtlasData M} {α P T : ℝ}
    (hη : HolderBound α univ
      (fun p : Point n => outerPatchBump 1 zero_lt_one (0 : Space n) p.1) P)
    (i : Fin A.count) (f : F05SourceZeroGraph A α T) :
    HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T) (F05PatchSource i f) ((2*P)*‖f‖) := by
  have hlocal := holderBound_mono (holderGraphFun_holderBound (f.val i))
    (inter_subset_left : F05Q A i T ∩ cylinder (closure (F05ModelOpen A i)) 0 T ⊆ F05Q A i T)
  have hprod := holderBound_smul_cutoff_extension
    (holderBound_mono hη (subset_univ (cylinder (closure (F05ModelOpen A i)) 0 T))) hlocal
    (F05_source_cutoff_zero_outside A i T)
  have hb : 2*P*‖f.val i‖ ≤ (2*P)*‖f‖ :=
    mul_le_mul_of_nonneg_left (norm_le_pi_norm f.val i) (by positivity [hη.1])
  apply holderBound_mono_const (f := F05PatchSource i f) ?_ hb
  unfold F05PatchSource
  simpa only [smul_eq_mul] using hprod

theorem F05_patch_source_map (A : AtlasData M) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ i : Fin A.count,
      ∃ P : F05SourceZeroGraph A α T →L[ℝ] compatibleHolderGraph α (F05ModelOpen A i) T,
        ‖P‖ ≤ C ∧
        (∀ f x, x ∈ closure (F05ModelOpen A i) → compatibleHolderFun (P f) (x,0) = 0) ∧
        (∀ f p, p ∈ F05Q A i T → ‖p.1‖ ≤ 3/2 →
          compatibleHolderFun (P f) p = holderGraphFun (f.val i) p) := by
  obtain ⟨B,hB,hη⟩ := outerPatchBump_global_holderBound hα hα1 zero_lt_one (0 : Space n)
  let C := 2*B
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T hT i
  let F := F05PatchSource (A := A) (α := α) (T := T) i
  have hbound := F05PatchSource_holderBound (A := A) (T := T) hη i
  have hadd (f g : F05SourceZeroGraph A α T) (p : Point n)
      (hp : p ∈ cylinder (closure (F05ModelOpen A i)) 0 T) : F (f+g) p = F f p+F g p :=
    F05PatchSource_add i f g p
  have hsmul (a : ℝ) (f : F05SourceZeroGraph A α T) (p : Point n)
      (hp : p ∈ cylinder (closure (F05ModelOpen A i)) 0 T) : F (a • f) p = a*F f p :=
    F05PatchSource_smul i a f p
  have hcorner (f : F05SourceZeroGraph A α T) (x : Space n)
      (hx : x ∈ frontier (F05ModelOpen A i)) : F f (x,0) = 0 := F05PatchSource_initial i f x
  let P := compatibleHolderGraphLift hα hT.le F hbound hadd hsmul hcorner
  refine ⟨P, compatibleHolderGraphLift_opNorm_le hα hT.le hC.le F hbound hadd hsmul hcorner, ?_, ?_⟩
  · intro f x hx
    rw [compatibleHolderGraphLift_eqOn hα hT.le F hbound hadd hsmul hcorner f ⟨hx,le_rfl,hT.le⟩]
    exact F05PatchSource_initial i f x
  · intro f p hp hn
    rw [compatibleHolderGraphLift_eqOn hα hT.le F hbound hadd hsmul hcorner f
      (F05Q_subset_model_cylinder A i T hp)]
    change outerPatchBump 1 zero_lt_one (0 : Space n) p.1 * holderGraphFun (f.val i) p = _
    have heq : outerPatchBump 1 zero_lt_one (0 : Space n) p.1 = 1 :=
      (outerPatchBump 1 zero_lt_one (0 : Space n)).one_of_mem_closedBall
        (by simpa only [outerPatchBump,Metric.mem_closedBall,dist_zero_right,mul_one] using hn)
    rw [heq,one_mul]

end Yau.Proofs.F05Aux
