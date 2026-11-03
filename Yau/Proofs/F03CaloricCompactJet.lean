import Yau.Proofs.F03CaloricRepresentativeLinearity
import Yau.Proofs.F03DirectionalLinearity
import Yau.Proofs.F03CompactTestFunctional

/-! Actual linear directional-jet maps into the full Banach space C(K). -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def caloricCompactJet
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (K : Set (Point d)) [CompactSpace K] (hKD : K ⊆ O ×ˢ Ioo l r) (w : List (Point d)) :
    CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB →ₗ[ℝ] C(K,ℝ) where
  toFun e := compactContinuousRestriction K
    (directionalWordDerivative (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) w)
    ((directionalWordDerivative_contDiffOn (hO.prod isOpen_Ioo)
      (caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e).1 w).continuousOn.mono hKD)
  map_add' e f := by
    ext p
    let F := caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll
    have heq : F (e+f) =ᶠ[𝓝 p.val] (fun q => F e q+F f q) := by
      filter_upwards [(hO.prod isOpen_Ioo).mem_nhds (hKD p.property)] with q hq
      exact caloricRepresentative_add hd O l r lam upper hO hlr a b hAB hEll e f hq
    change directionalWordDerivative (F (e+f)) w p.val =
      directionalWordDerivative (F e) w p.val+directionalWordDerivative (F f) w p.val
    rw [(directionalWordDerivative_eventuallyEq heq w).eq_of_nhds]
    exact directionalWordDerivative_add_on (hO.prod isOpen_Ioo)
      (caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e).1
      (caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll f).1 w (hKD p.property)
  map_smul' c e := by
    ext p
    let F := caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll
    have heq : F (c • e) =ᶠ[𝓝 p.val] (fun q => c*F e q) := by
      filter_upwards [(hO.prod isOpen_Ioo).mem_nhds (hKD p.property)] with q hq
      exact caloricRepresentative_const_smul hd O l r lam upper hO hlr a b hAB hEll c e hq
    change directionalWordDerivative (F (c • e)) w p.val=c*directionalWordDerivative (F e) w p.val
    rw [(directionalWordDerivative_eventuallyEq heq w).eq_of_nhds,directionalWordDerivative_const_mul]

end Yau.Proofs.F03Aux
