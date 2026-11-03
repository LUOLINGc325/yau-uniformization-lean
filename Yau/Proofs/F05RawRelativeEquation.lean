import Yau.Proofs.F05RawChartEquation
import Yau.Proofs.F05SmoothClosedSlabC2
import Yau.Proofs.F05BootstrapNative

/-! The intrinsic equation on a later solution domain becomes the exact
computed relative equation on an arbitrary fixed full raw receiving ball.
All derivatives are identified from actual smoothness on the same slab. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_raw_relative_nonlinear_equation {O V : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (R w : M.Carrier → ℝ → ℝ)
    (i : Fin A.count) {l T : ℝ} (hlT : l < T)
    (hDomain : lift A i '' Metric.ball 0 3 ⊆ closure V)
    (hSmooth : ContDiffOn ℝ ∞ (pull A i w) (Metric.ball 0 3 ×ˢ Icc l T))
    (hEquation : ∀ x ∈ closure V, ∀ t ∈ Icc l T,
      derivWithin (w x) (Icc l T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*R x t) :
    ∀ z ∈ region none (5/2) ×ˢ Icc l T,
      F05RelT (Icc l T) (pull A i w) z = Real.exp (-pull A i w z)*
        ((∑ a,∑ b,flatA (h z.2) A i z a b*
            F05RelDD (region none (5/2)) (pull A i w) z (realVec a) (realVec b))+
          ∑ a,flatB (h z.2) A i z a*F05RelD (region none (5/2)) (pull A i w) z (realVec a))+
        (1-Real.exp (-pull A i w z))*pull A i R z := by
  have hSub : region (n := n) none (5/2) ⊆ Metric.ball 0 3 := by
    intro z hz
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hz.1]
  have hC2 := F05_smooth_closed_slab_c2 Metric.isOpen_ball hSub hlT le_rfl hSmooth
  have hX := F05_region_uniqueDiffOn (n := n) none (by norm_num : (0 : ℝ) < 5/2)
  intro z hz
  have hSpatial : ContDiffAt ℝ 2 (fun y => w (lift A i y) z.2) z.1 :=
    hC2.2.2.2.2.1 z hz
  have hLap := F05_flattened_laplacian_C2 hA (h z.2) i (fun y => w y z.2) (hSub hz.1) hSpatial
  change laplacian (h z.2) (fun y => w y z.2) (lift A i z.1) =
    (∑ a,∑ b,flatA (h z.2) A i z a b*spatialDD (pull A i w) z (realVec a) (realVec b))+
      ∑ a,flatB (h z.2) A i z a*spatialD (pull A i w) z (realVec a) at hLap
  rw [F05RelDD_eq_spatialDD hX hz.1 (fun y hy => hC2.2.2.2.2.1 (y,z.2) ⟨hy,hz.2⟩),
    F05RelD_eq_spatialD (hX z.1 hz.1) (hSpatial.differentiableAt (by norm_num)),← hLap]
  exact hEquation (lift A i z.1) (hDomain ⟨z.1,hSub hz.1,rfl⟩) z.2 hz.2

end Yau.Proofs.F05Aux
