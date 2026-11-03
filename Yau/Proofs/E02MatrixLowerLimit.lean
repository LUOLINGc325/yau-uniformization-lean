import Yau.Proofs.E02HermitianPerturbation

open Matrix Filter
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- A fixed positive B controls a converging Hermitian family with an
arbitrarily small loss in its scalar coefficient. -/
theorem eventually_matrix_lower_of_tendsto {ι : Type*} {l : Filter ι} {n : ℕ}
    (A : ι → Herm n) (A₀ B : Herm n) (hB : B.PosDef) (c : ℝ)
    (hLower : (A₀-(c : ℂ) • B).PosSemidef)
    (hA : ∀ᶠ i in l, (A i).IsHermitian) (hlim : Tendsto A l (𝓝 A₀))
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ i in l, (A i-((c-r : ℝ) : ℂ) • B).PosSemidef := by
  have hCenter : (A₀-((c-r : ℝ) : ℂ) • B).PosDef := by
    have hPos : ((r : ℂ) • B).PosDef := hB.smul (RCLike.ofReal_pos.mpr hr)
    have hp := Matrix.PosDef.posSemidef_add hLower hPos
    convert hp using 1
    push_cast
    module
  have hSelf : IsSelfAdjoint ((c-r : ℝ) : ℂ) := by simp [isSelfAdjoint_iff]
  have hHerm : ∀ᶠ i in l, (A i-((c-r : ℝ) : ℂ) • B).IsHermitian :=
    hA.mono (fun _ hi => hi.sub (hB.isHermitian.smul hSelf))
  have hLimit : Tendsto (fun i => A i-((c-r : ℝ) : ℂ) • B) l
      (𝓝 (A₀-((c-r : ℝ) : ℂ) • B)) := hlim.sub tendsto_const_nhds
  exact (eventually_posDef_of_tendsto_hermitian _ _ hCenter hHerm hLimit).mono
    (fun _ hi => hi.posSemidef)

theorem eventually_finite_matrix_lower {ι κ : Type*} [Finite κ] {l : Filter ι} {n : ℕ}
    (A : κ → ι → Herm n) (A₀ : κ → Herm n) (B : Herm n) (hB : B.PosDef) (c : ℝ)
    (hLower : ∀ j, (A₀ j-(c : ℂ) • B).PosSemidef)
    (hA : ∀ j, ∀ᶠ i in l, (A j i).IsHermitian) (hlim : ∀ j, Tendsto (A j) l (𝓝 (A₀ j)))
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ i in l, ∀ j, (A j i-((c-r : ℝ) : ℂ) • B).PosSemidef := by
  apply eventually_all.mpr
  intro j
  exact eventually_matrix_lower_of_tendsto (A j) (A₀ j) B hB c (hLower j) (hA j) (hlim j) hr

end Yau.NodeProofs.E02Aux
