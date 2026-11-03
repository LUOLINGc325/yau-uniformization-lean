import Yau.Proofs.F05FlowBarriers
import Yau.Proofs.F05JetOperator

/-! The actual paper corner data give an all-initial-zero nonlinear source,
throughout the original domain, before any boundary contraction is applied. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.Blueprint
variable {n : ℕ} {M : ComplexManifold n}

def F05NonlinearCorrection (h : ℝ → HermitianField M) (T : ℝ)
    (p z : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  (Real.exp (-(p x t+z x t))-Real.exp (-p x t))*
    laplacian (h t) (fun y => p y t+z y t) x+
      (1-Real.exp (-(p x t+z x t)))*scalarCurvature (h t) x-
        F05IntrinsicLinearOperator (fun x t => Real.exp (-p x t)) h T p x t

theorem F05_nonlinear_correction_initial (h : ℝ → HermitianField M) (T α : ℝ)
    (p z : M.Carrier → ℝ → ℝ)
    (hP0 : ∀ x, p x 0 = α) (hZ0 : ∀ x, z x 0 = 0)
    (hTime : ∀ x, derivWithin (p x) (Icc 0 T) 0 =
      (1-Real.exp (-α))*scalarCurvature (h 0) x) (x : M.Carrier) :
    F05NonlinearCorrection h T p z x 0 = 0 := by
  have hLap : laplacian (h 0) (fun y => p y 0) x = 0 := by
    have hEq : (fun y => p y 0) = (fun _ => α) := funext hP0
    rw [hEq]
    exact Yau.LeafProofs.L18Aux.laplacian_const (h 0) α x
  unfold F05NonlinearCorrection F05IntrinsicLinearOperator
  rw [hP0 x,hZ0 x,add_zero,sub_self,zero_mul,hLap,mul_zero,sub_zero,hTime]
  ring

theorem F05_flow_corner_nonlinear_initial {X : KahlerManifold n}
    (o : Pt X) (h : Flow X) (U P ρ : STF X) (hloc : LocalizedFlow X o h U P ρ)
    {T : ℝ} (hT : 0 < T) (α δ : ℝ) (ζ : ℝ → ℝ)
    (hζ : ζ =ᶠ[𝓝 0] (fun _ => 1)) (z : STF X) (hZ0 : ∀ x, z x 0 = 0) (x : Pt X) :
    F05NonlinearCorrection h T (flowCornerBoundary X ρ α δ ζ) z x 0 = 0 := by
  apply F05_nonlinear_correction_initial h T α _ z
    (flowCornerBoundary_initial o h U P ρ hloc α δ ζ) hZ0
  intro y
  have hh := (flowCornerBoundary_initial_derivative o h U P ρ hloc α δ ζ hζ y).mono
    (show Icc 0 T ⊆ Ici 0 from fun t ht => ht.1)
  have hDeriv := hh.derivWithin (uniqueDiffOn_Icc hT 0 ⟨le_rfl,hT.le⟩)
  simpa only [hloc.1.1] using hDeriv

end Yau.Proofs.F05Aux
