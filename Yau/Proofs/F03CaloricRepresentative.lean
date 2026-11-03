import Yau.Proofs.F03CaloricWeakSpace
import Yau.LeafProofs.L16InteriorSmoothing

/-! Native smoothing and uniqueness on the explicitly complete weak-caloric space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem caloricSpace_exists_smoothRepresentative
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB) :
    ∃ v : Point d → ℝ, ContDiffOn ℝ ∞ v (O ×ˢ Ioo l r) ∧
      (e.val.1 : Point d → ℝ) =ᵐ[volume.restrict (O ×ˢ Ioo l r)] v ∧
      ∀ p ∈ O ×ˢ Ioo l r, linearOp (O ×ˢ Ioo l r) a b v p=0 := by
  obtain ⟨v,hv,hAE,hEq⟩ := LeafProofs.L16Interior.homogeneousInteriorSmoothing d hd O l r lam upper hO hlr
    a b (e.val.1 : Point d → ℝ) (fun p i => e.val.2 i p) hAB hEll
    (caloricSpace_localEnergy O (Ioo l r) (hO.prod isOpen_Ioo) a b hAB e)
    (caloricSpace_weakEquation O (Ioo l r) (hO.prod isOpen_Ioo) a b hAB e)
  rw [productVolume_eq_restrict] at hAE
  exact ⟨v,hv,hAE,hEq⟩

def caloricRepresentative
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB) : Point d → ℝ :=
  (caloricSpace_exists_smoothRepresentative hd O l r lam upper hO hlr a b hAB hEll e).choose

theorem caloricRepresentative_spec
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB) :
    ContDiffOn ℝ ∞ (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) (O ×ˢ Ioo l r) ∧
      (e.val.1 : Point d → ℝ) =ᵐ[volume.restrict (O ×ˢ Ioo l r)]
        caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e ∧
      ∀ p ∈ O ×ˢ Ioo l r, linearOp (O ×ˢ Ioo l r) a b
        (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) p=0 :=
  (caloricSpace_exists_smoothRepresentative hd O l r lam upper hO hlr a b hAB hEll e).choose_spec

theorem caloricRepresentative_eqOn_of_ae
    (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)
    (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB)
    (v : Point d → ℝ) (hv : ContinuousOn v (O ×ˢ Ioo l r))
    (hAE : (e.val.1 : Point d → ℝ) =ᵐ[volume.restrict (O ×ˢ Ioo l r)] v) :
    EqOn (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e) v (O ×ˢ Ioo l r) := by
  have hs := caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e
  exact Measure.eqOn_open_of_ae_eq (hs.2.1.symm.trans hAE) (hO.prod isOpen_Ioo) hs.1.continuousOn hv

end Yau.Proofs.F03Aux
