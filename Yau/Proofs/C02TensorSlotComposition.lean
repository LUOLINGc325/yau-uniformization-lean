import Yau.LeafProofs.L23TensorPullback

noncomputable section
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L23Aux
variable {n r : ℕ}

theorem tensor_comp_cons (T : RealTensorForm n (r + 1))
    (Q : ComplexVector n →L[ℝ] ComplexVector n) (u : ComplexVector n)
    (V : Fin r → ComplexVector n) :
    (T.compContinuousLinearMap (fun _ => Q)) (Fin.cons u V) =
      T (Fin.cons (Q u) (fun i => Q (V i))) := by
  change T (fun i : Fin (r + 1) => Q ((Fin.cons u V : Fin (r + 1) → ComplexVector n) i)) = _
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

end Yau.Blueprint.C02Proof
