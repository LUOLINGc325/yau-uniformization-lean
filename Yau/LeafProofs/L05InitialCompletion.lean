import Yau.LeafProofs.L05InitialTime

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem schauderBound_across_zero {n : ℕ} {O : Set (Space n)} {T gamma C : ℝ}
    (hO : IsOpen O) (hT : 0 < T) (hgamma : 0 < gamma) {u : Point n → ℝ}
    (hu : C2 (cylinder O (-T) T) u)
    (hz : ∀ p ∈ cylinder O (-T) T, p.2 ≤ 0 → u p=0)
    (hC : 0 ≤ C)
    (hlo : ∀ p ∈ O ×ˢ Set.Ioc 0 T, |u p| ≤ C ∧ ‖spatialD u p‖ ≤ C)
    (hDD : HolderBound gamma (O ×ˢ Set.Ioc 0 T) (spatialDD u) C)
    (hDt : HolderBound gamma (O ×ˢ Set.Ioc 0 T) (timeD (cylinder O (-T) T) u) C) :
    SchauderBound gamma (cylinder O (-T) T) u C := by
  have hDz (p : Point n) (hp : p ∈ cylinder O (-T) T) (ht : p.2 ≤ 0) :
      spatialD u p=0 ∧ spatialDD u p=0 := by
    exact spatial_jets_zero_of_slice hO hp.1 (fun y hy => hz (y,p.2) ⟨hy,hp.2⟩ ht)
  refine ⟨hu,hC,?_,
    holderBound_across_zero hT hgamma hu.2.2.1 (fun p hp ht => (hDz p hp ht).2) hDD,
    holderBound_across_zero hT hgamma hu.2.2.2.1 (fun p hp ht => timeD_zero_of_nonpos hT hu hz hp ht) hDt⟩
  intro p hp
  by_cases ht : 0 < p.2
  · exact hlo p ⟨hp.1,ht,hp.2.2⟩
  · have ht' := le_of_not_gt ht
    rw [hz p hp ht',(hDz p hp ht').1,abs_zero,norm_zero]
    exact ⟨hC,hC⟩

end Yau.LeafProofs.L05Aux
