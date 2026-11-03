import Yau.Proofs.E02LocalTest
import Yau.Proofs.E02StrictifyNeighborhood

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The original lower germ supplies ONE finite C² open base/time
neighborhood, with strict inequality away from its original center. -/
theorem exists_original_base_localization {n : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (a : ComplexVector n × ℝ) (hz : a.1 ∈ chartTarget x) (ht : a.2 ∈ Ioo 0 T)
    (f : ComplexVector n × ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f a)
    (hLower : ∀ᶠ p in 𝓝 a, f p ≤ ellipsoidLogDet X h T x p.1 p.2) :
    ∃ V : Set (ComplexVector n × ℝ), IsOpen V ∧ a ∈ V ∧
      V ⊆ chartTarget x ×ˢ Ioo 0 T ∧ ContDiffOn ℝ 2 (baseTimeStrictify f a) V ∧
      (∀ p ∈ V, baseTimeStrictify f a p ≤ ellipsoidLogDet X h T x p.1 p.2) ∧
      (∀ p ∈ V, p ≠ a → baseTimeStrictify f a p < ellipsoidLogDet X h T x p.1 p.2) := by
  obtain ⟨V₂,hV₂,ha₂,hf₂⟩ := smooth_germ_open_C2 hf
  obtain ⟨V₁,hLower₁,hV₁,ha₁⟩ := eventually_nhds_iff.mp hLower
  let D : Set (ComplexVector n × ℝ) := chartTarget x ×ˢ Ioo 0 T
  have hD : IsOpen D := (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioo
  let V := (V₂ ∩ V₁) ∩ D
  have hSub : V ⊆ V₂ := fun p hp => hp.1.1
  refine ⟨V,(hV₂.inter hV₁).inter hD,⟨⟨ha₂,ha₁⟩,hz,ht⟩,
    (fun p hp => hp.2),baseTimeStrictify_contDiffOn_two f a V (hf₂.mono hSub),?_,?_⟩
  · intro p hp
    exact (baseTimeStrictify_le f a p).trans (hLower₁ p hp.1.2)
  · intro p hp hNe
    exact baseTimeStrictify_strict_lower (f := f)
      (g := fun q => ellipsoidLogDet X h T x q.1 q.2) (a := a) (p := p)
      (hLower₁ p hp.1.2) hNe

end Yau.NodeProofs.E02Aux
