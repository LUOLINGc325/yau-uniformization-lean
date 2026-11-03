import Yau.Proofs.V03Dirichlet

/-! Convergence in the original Fourier seminorm preserves its quadratic
energy. This is the scalar Hilbert-space step in radial regularization. -/

open scoped Topology lp
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_sub_ne_top {u v : ℝ → ℂ}
    (hu : Continuous u) (hv : Continuous v)
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤) :
    boundaryDSq (fun θ (_ : Unit) => u θ - v θ) ≠ ⊤ := by
  apply (dirichletCoeff_mem_iff _).mp
  have hm := ((dirichletCoeff_mem_iff u).mpr huf).sub
    ((dirichletCoeff_mem_iff v).mpr hvf)
  convert hm using 1
  funext k
  dsimp only [dirichletCoeff, Pi.sub_apply]
  rw [circleFourier_sub hu hv, mul_sub]

theorem dirichletVector_sub {u v : ℝ → ℂ} (hu : Continuous u) (hv : Continuous v)
    (huf : boundaryDSq (fun θ (_ : Unit) => u θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤)
    (hs : boundaryDSq (fun θ (_ : Unit) => u θ - v θ) ≠ ⊤) :
    dirichletVector (fun θ => u θ - v θ) hs =
      dirichletVector u huf - dirichletVector v hvf := by
  apply Subtype.ext
  funext k
  change dirichletCoeff (fun θ => u θ - v θ) k = dirichletCoeff u k - dirichletCoeff v k
  rw [dirichletCoeff, circleFourier_sub hu hv]
  exact mul_sub _ _ _

theorem boundaryDSq_toReal_tendsto_of_sub {α : Type*} {l : Filter α}
    (u : α → ℝ → ℂ) (v : ℝ → ℂ) (hu : ∀ a, Continuous (u a)) (hv : Continuous v)
    (huf : ∀ a, boundaryDSq (fun θ (_ : Unit) => u a θ) ≠ ⊤)
    (hvf : boundaryDSq (fun θ (_ : Unit) => v θ) ≠ ⊤)
    (hsub : Tendsto (fun a =>
      (boundaryDSq (fun θ (_ : Unit) => u a θ - v θ)).toReal) l (𝓝 (0 : ℝ))) :
    Tendsto (fun a => (boundaryDSq (fun θ (_ : Unit) => u a θ)).toReal) l
      (𝓝 (boundaryDSq (fun θ (_ : Unit) => v θ)).toReal) := by
  have hsf := fun a => boundaryDSq_sub_ne_top (hu a) hv (huf a) hvf
  have hn : ∀ a, Real.sqrt (boundaryDSq (fun θ (_ : Unit) => u a θ - v θ)).toReal =
      ‖dirichletVector (u a) (huf a) - dirichletVector v hvf‖ := by
    intro a
    rw [← dirichletVector_norm _ (hsf a),
      dirichletVector_sub (hu a) hv (huf a) hvf (hsf a)]
  have hnorm : Tendsto (fun a =>
      ‖dirichletVector (u a) (huf a) - dirichletVector v hvf‖) l (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, hn, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsub
  have hvec : Tendsto (fun a => dirichletVector (u a) (huf a)) l
      (𝓝 (dirichletVector v hvf)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  simpa only [dirichletVector_norm_sq] using hvec.norm.pow 2

end Yau.Blueprint.V03Proof
