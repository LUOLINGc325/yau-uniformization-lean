import Yau.Proofs.F05ClosedChartEquation

/-! The actual full closed-chart equation implies the original intrinsic
nonlinear PDE at every point of the physical closure. -/

open Set
noncomputable section
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_intrinsic_nonlinear_of_closed_charts {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (w : M.Carrier → ℝ → ℝ)
    {l r : ℝ} (hw : ∀ i, C2 (cylinder (F05D A i) l r) (pull A i w))
    (hEq : ∀ i z, z ∈ cylinder (F05D A i) l r →
      timeD (cylinder (F05D A i) l r) (pull A i w) z = Real.exp (-pull A i w z)*
        ((∑ a,∑ b,flatA (h z.2) A i z a b*spatialDD (pull A i w) z (realVec a) (realVec b))+
          ∑ a,flatB (h z.2) A i z a*spatialD (pull A i w) z (realVec a))+
        (1-Real.exp (-pull A i w z))*scalarCurvature (h z.2) (lift A i z.1)) :
    ∀ x ∈ closure O, ∀ t ∈ Icc l r,
      derivWithin (w x) (Icc l r) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*scalarCurvature (h t) x := by
  intro x hx t ht
  obtain ⟨i,z,hz,hzx⟩ := F05_cover hA hx
  have hzQ : (z,t) ∈ cylinder (F05D A i) l r := ⟨hz,ht⟩
  have hLap := F05_flattened_laplacian_C2 hA (h t) i (fun y => w y t)
    (F05D_mem_ball hz) ((hw i).2.2.2.2.1 (z,t) hzQ)
  have hLocal := hEq i (z,t) hzQ
  have hTime := F05_timeD_pull_interval A i l r w (p := (z,t)) hz
  have hScalar := hTime.symm.trans hLocal
  have hRHS := congrArg (fun L : ℝ => Real.exp (-w (lift A i z) t)*L+
    (1-Real.exp (-w (lift A i z) t))*scalarCurvature (h t) (lift A i z)) hLap
  have hPoint := hScalar.trans hRHS.symm
  simpa only [hzx] using hPoint

end Yau.Proofs.F05Aux
