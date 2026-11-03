import Yau.Proofs.F05BootstrapBase
import Yau.Proofs.F05BootstrapRelativeRestriction
import Yau.Proofs.F05BootstrapLocalFields
import Yau.Proofs.F05FlattenedLaplacian

/-! The supplied ambient spatial C2 field identifies the actual computed
positive-time relative jets, and transports the original nonlinear PDE. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_native_positive_jets {ν : Option (RIdx n)} {T : ℝ} {v : Point n → ℝ}
    (hv : C2 (cylinder (region ν 2) 0 T) v) {z : Point n} (hz : z ∈ F05PosPatch ν T) :
    F05RelD (F05PosSpace ν) v z = spatialD v z ∧
      F05RelDD (F05PosSpace ν) v z = spatialDD v z ∧
      F05RelT (Ioc 0 T) v z = F05RelT (Icc 0 T) v z := by
  have hSub : F05PosSpace ν ⊆ region ν 2 := fun x hx =>
    F05_posSpace_mem_region hx (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hx.2).le)
  have hzFull : z ∈ cylinder (region ν 2) 0 T := ⟨hSub hz.1,hz.2.1.le,hz.2.2⟩
  have hEq := F05_relative_restriction_jets (F05_region_uniqueDiffOn ν (by norm_num))
    (F05_posSpace_uniqueDiffOn ν) (uniqueDiffOn_Ioc 0 T) hSub Ioc_subset_Icc_self
    (F05_native_c2_to_relative (F05_region_uniqueDiffOn ν (by norm_num)) hv) hz
  refine ⟨hEq.1.trans ?_,hEq.2.1.trans ?_,hEq.2.2⟩
  · exact F05RelD_eq_spatialD (F05_region_uniqueDiffOn ν (by norm_num) z.1 hzFull.1)
      ((hv.2.2.2.2.1 z hzFull).differentiableAt (by norm_num))
  · exact F05RelDD_eq_spatialDD (F05_region_uniqueDiffOn ν (by norm_num)) hzFull.1
      (fun x hx => hv.2.2.2.2.1 (x,z.2) ⟨hx,hzFull.2⟩)

theorem F05_original_nonlinear_chart_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (R w : M.Carrier → ℝ → ℝ)
    {T : ℝ} (i : Fin A.count) (hw : C2 (F05Q A i T) (pull A i w))
    (hEquation : ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (w x) (Icc 0 T) t =
        Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
          (1-Real.exp (-w x t))*R x t) :
    ∀ z ∈ F05PosPatch (A.normal i) T,
      F05RelT (Ioc 0 T) (pull A i w) z = Real.exp (-pull A i w z)*
        ((∑ j,∑ k,flatA (h z.2) A i z j k*
          F05RelDD (F05PosSpace (A.normal i)) (pull A i w) z (realVec j) (realVec k))+
          ∑ j,flatB (h z.2) A i z j*F05RelD (F05PosSpace (A.normal i)) (pull A i w) z (realVec j))+
        (1-Real.exp (-pull A i w z))*pull A i R z := by
  intro z hz
  have hzD : z.1 ∈ F05D A i := F05_posSpace_mem_region hz.1
    (by simpa only [dist_zero_right] using (Metric.mem_ball.mp hz.1.2).le)
  have hzQ : z ∈ F05Q A i T := ⟨hzD,hz.2.1.le,hz.2.2⟩
  have hJets := F05_native_positive_jets hw hz
  have hLap := F05_flattened_laplacian_C2 hA (h z.2) i (fun y => w y z.2)
    (F05D_mem_ball hzD) (hw.2.2.2.2.1 z hzQ)
  have hPDE := hEquation (lift A i z.1) (F05D_lift_mem_closure hA hzD) z.2 hzQ.2
  rw [hJets.2.2,hJets.2.1,hJets.1]
  change derivWithin (w (lift A i z.1)) (Icc 0 T) z.2 = _
  rw [hPDE,hLap]
  rfl

end Yau.Proofs.F05Aux
