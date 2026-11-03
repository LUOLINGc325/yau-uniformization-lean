import Yau.Proofs.F05AtlasHomeomorph
import Yau.Proofs.F05Partition

/-! A true open flattened-chart profile extension pulls back to a true
open manifold extension, with exact equality on the physical closed set. -/

open Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_atlas_equiv_contMDiffOn {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) :
    ContMDiffOn 𝓘(ℝ,Space n) 𝓘(ℝ,Space n) ∞ (F05AtlasEquiv hA i) (F05AtlasEquiv hA i).source := by
  letI := Yau.LeafProofs.L12Aux.manifold_realSmooth M
  have hChart : ContMDiffOn 𝓘(ℝ,Space n) 𝓘(ℝ,Space n) ∞
      (chartAt (Space n) (A.center i)) (chartAt (Space n) (A.center i)).source :=
    contMDiffOn_chart (I := 𝓘(ℝ,Space n)) (n := ∞) (x := A.center i)
  have hF : ContMDiffOn 𝓘(ℝ,Space n) 𝓘(ℝ,Space n) ∞ (A.forward i) (A.source i) :=
    (hA.1 i).2.2.1.contMDiffOn
  exact hF.comp (hChart.mono inter_subset_left) (fun y hy => hy.2)

theorem F05_local_profile_model_to_manifold {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) {z : Space n} (hz : z ∈ Metric.ball 0 3)
    {V : Set (Space n)} (hV : IsOpen V) (hzV : z ∈ V) {F : Space n → ℝ}
    (hF : ContDiffOn ℝ ∞ F V) (f : M.Carrier → ℝ)
    (hEq : ∀ y ∈ V, y ∈ Metric.ball 0 3 → lift A i y ∈ closure O → F y = f (lift A i y)) :
    ∃ (U : Set M.Carrier) (g : M.Carrier → ℝ), IsOpen U ∧ lift A i z ∈ U ∧
      ContMDiffOn 𝓘(ℝ,Space n) 𝓘(ℝ,ℝ) ∞ g U ∧ EqOn g f (closure O∩U) := by
  letI := Yau.LeafProofs.L12Aux.manifold_realSmooth M
  let e := F05AtlasEquiv hA i
  let U := e.source ∩ e ⁻¹' V
  have hzTarget : z ∈ e.target := by rw [F05AtlasEquiv_target]; exact hz
  have hLift : lift A i z = e.symm z := by rw [F05AtlasEquiv_inverse]
  have hxU : lift A i z ∈ U := by
    rw [hLift]
    refine ⟨e.map_target hzTarget,?_⟩
    change e (e.symm z) ∈ V
    rwa [e.right_inv hzTarget]
  have hg : ContMDiffOn 𝓘(ℝ,Space n) 𝓘(ℝ,ℝ) ∞ (F ∘ e) U :=
    hF.contMDiffOn.comp ((F05_atlas_equiv_contMDiffOn hA i).mono inter_subset_left)
      (fun y hy => hy.2)
  refine ⟨U,F ∘ e,e.isOpen_inter_preimage hV,hxU,hg,?_⟩
  intro y hy
  have hyTarget := e.map_source hy.2.1
  have hyBall : e y ∈ Metric.ball 0 3 := by rwa [F05AtlasEquiv_target] at hyTarget
  have hLiftY : lift A i (e y) = y := by
    rw [← F05AtlasEquiv_inverse hA i]
    exact e.left_inv hy.2.1
  have h := hEq (e y) hy.2.2 hyBall (by rw [hLiftY]; exact hy.1)
  simpa only [Function.comp_apply,hLiftY] using h

end Yau.Proofs.F05Aux
