import Yau.Proofs.F05BootstrapDefinitions

/-! The spatial derivative of a translated relative field is its actual
within derivative on the original set. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_shifted_relative_hasFDeriv {X Y : Set (Space n)} {f : Point n → V} {t : ℝ}
    (hF : DifferentiableOn ℝ (fun x => f (x,t)) Y) (v : Space n)
    (hMap : MapsTo (fun x => x+v) X Y) {x : Space n} (hx : x ∈ X) :
    HasFDerivWithinAt (fun y => f (y+v,t)) (F05RelD Y f (x+v,t)) X x := by
  have hInner : HasFDerivWithinAt (fun y : Space n => y+v)
      (ContinuousLinearMap.id ℝ (Space n)) X x := ((hasFDerivAt_id x).add_const v).hasFDerivWithinAt
  simpa only [F05RelD,ContinuousLinearMap.comp_id,Function.comp_def] using
    (hF (x+v) (hMap hx)).hasFDerivWithinAt.comp x hInner hMap

end Yau.Proofs.F05Aux
