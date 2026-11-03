import Yau.LeafProofs.L05DiniKernelDefinitions

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic
open L16Aux

local instance l05DiniKernelRepresentationDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelRepresentationDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05DiniKernelRepresentationHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05DiniKernelRepresentationHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem constant_causal_representation {n : ℕ} {T eta F W ell L : ℝ} {A : Mat n}
    (S : Space n ≃L[ℝ] Space n)
    (hS : ∀ H : DiniHessian n,
      (∑ k : Yau.RIdx n, H (S (Yau.realVec k)) (S (Yau.realVec k)))=
        ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*H (Yau.realVec i) (Yau.realVec j))
    {g w : Point n → ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (he : 0 < eta) (he1 : eta < 1)
    (hEll : Elliptic (cylinder Set.univ 0 T) (fun _ => A) ell L)
    (hg : HolderBound eta (cylinder Set.univ 0 T) g F)
    (hw : C2 (cylinder Set.univ 0 T) w)
    (hwB : ∀ p ∈ cylinder Set.univ 0 T, |w p| ≤ W) (hw0 : ∀ x : Space n, w (x,0)=0)
    (hPDE : ∀ p ∈ Set.univ ×ˢ Set.Ioc (0:ℝ) T,
      linearOp (cylinder Set.univ 0 T) (fun _ => A) (fun _ _ => 0) w p=g p) :
    Set.EqOn w (constantHeatDuhamel S g) (cylinder Set.univ 0 T) := by
  obtain ⟨C,hC,hSch⟩ := constantHeatDuhamel_schauderBound (n := n) he he1
  have hU := hSch S T F hT hT1 g hg
  apply bounded_wholeSpace_unique (b := fun _ _ => 0) hT hw hU.1 hEll (le_refl (0:ℝ))
    (fun p hp i => by simp) hwB (fun p hp => (hU.2.2.1 p hp).1)
  · intro x
    rw [hw0 x,constantHeatDuhamel_initial]
  · intro p hp
    rw [hPDE p hp,constantHeatDuhamel_linearOp S hS he he1 hT hT1 hg
      ⟨Set.mem_univ _,hp.2.1.le,hp.2.2⟩]

end Yau.LeafProofs.L05Aux
