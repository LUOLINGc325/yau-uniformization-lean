import Yau.Proofs.F01UniformTensorFirstJet
import Yau.Proofs.F01HolderComposition

/-! Currying the next actual spatial tensor jet gives the Holder
bound for the preceding jet of the spatial derivative, with exactly the
same constant. All tensor norms and differences are preserved. -/
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem holderBound_spatial_tensor_derivative {Q : Set (Point n)} {β C : ℝ}
    {f : Point n → F} (k : ℕ)
    (hf : HolderBound β Q (fun p =>
      iteratedFDeriv ℝ (k + 1) (fun z => f (z, p.2)) p.1) C) :
    HolderBound β Q (fun p => iteratedFDeriv ℝ k
      (fun z => fderiv ℝ (fun y => f (y, p.2)) z) p.1) C := by
  let L := continuousMultilinearCurryRightEquiv' ℝ k (Space n) F
  have he (p : Point n) : L.symm (iteratedFDeriv ℝ k
      (fun z => fderiv ℝ (fun y => f (y, p.2)) z) p.1) =
      iteratedFDeriv ℝ (k + 1) (fun z => f (z, p.2)) p.1 :=
    (iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (n := k)
      (f := fun z => f (z, p.2)) (x := p.1)).symm
  refine ⟨hf.1, ?_, ?_⟩
  · intro p hp
    rw [← L.symm.norm_map, he]
    exact hf.2.1 p hp
  · intro p hp q hq
    let g := fun p : Point n => iteratedFDeriv ℝ k
      (fun z => fderiv ℝ (fun y => f (y, p.2)) z) p.1
    change ‖g p - g q‖ ≤ _
    calc
      ‖g p - g q‖ = dist (g p) (g q) := (dist_eq_norm _ _).symm
      _ = dist (L.symm (g p)) (L.symm (g q)) := (L.symm.isometry.dist_eq _ _).symm
      _ = ‖iteratedFDeriv ℝ (k + 1) (fun z => f (z, p.2)) p.1 -
          iteratedFDeriv ℝ (k + 1) (fun z => f (z, q.2)) q.1‖ := by
        rw [he, he, dist_eq_norm]
      _ ≤ _ := hf.2.2 p hp q hq

end Yau.NodeProofs.F01Aux
