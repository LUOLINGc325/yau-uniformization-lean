import Yau.Proofs.P06HodgeRegularityWeakTransport
import Yau.Proofs.P06HodgeRegularityRealCoordinates
import Yau.Proofs.P06HodgeRegularityFiniteJets

/-! The actual Hodge real basis becomes the standard finite coordinate
basis under the previously proved measure-preserving equivalence. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.LeafProofs.L16Aux

theorem hodgeRegularityFinEquiv_apply_basis (n : ℕ) (i : RIdx n) :
    hodgeRegularityFinEquiv n (realModelBasis n i) =
      Pi.single ((Fintype.equivFin (RIdx n)) i) 1 := by
  classical
  ext j
  simp only [hodgeRegularityFinEquiv,hodgeRegularityFinReindex,hodgeRegularityRealEquiv,
    LinearEquiv.piCongrLeft,LinearEquiv.piCongrLeft']
  by_cases h : j = (Fintype.equivFin (RIdx n)) i
  · subst j
    simp
  · have h' : (Fintype.equivFin (RIdx n)).symm j ≠ i := by
      intro hh
      apply h
      rw [← hh,Equiv.apply_symm_apply]
    simp [Finsupp.single_apply,Pi.single_apply,h,h',Ne.symm h,Ne.symm h']

theorem hodgeRegularityFiniteCoordinateWeakJet {n : ℕ} {α : Type*}
    (s : ℕ) (U : ComplexVector n → α → ℝ)
    (J : List (RIdx n) → ComplexVector n → α → ℝ)
    (hJ : regularityWeakJet (lebesgueC n) Set.univ (realModelBasis n) s U J)
    (hcJ : ∀ w, w.length ≤ s → ∀ c, HasCompactSupport (fun z => J w z c)) (c : α) :
    FiniteCoordinateWeakJet s (fun y => U ((hodgeRegularityFinEquiv n).symm y) c)
      (fun w y => J (w.map (Fintype.equivFin (RIdx n)).symm)
        ((hodgeRegularityFinEquiv n).symm y) c) := by
  classical
  have hdir (i : Fin (Fintype.card (RIdx n))) :
      hodgeRegularityFinEquiv n (realModelBasis n ((Fintype.equivFin (RIdx n)).symm i)) = Pi.single i 1 := by
    rw [hodgeRegularityFinEquiv_apply_basis]
    simp only [Equiv.apply_symm_apply]
  have ht := regularityWeakJet_transport (lebesgueC n) volume (hodgeRegularityFinEquiv n)
    (hodgeRegularityFinEquiv_measurePreserving n) (realModelBasis n) (fun i => Pi.single i 1)
    (Fintype.equivFin (RIdx n)).symm hdir s U J hJ
  refine ⟨?_,?_,?_⟩
  · funext y
    exact congrFun (congrFun ht.1 y) c
  · intro w hw
    refine ⟨?_,?_⟩
    · simpa only [Measure.restrict_univ] using ht.2.1 w hw c
    · exact (hcJ (w.map _) (by simpa only [List.length_map] using hw) c).comp_homeomorph
        (hodgeRegularityFinEquiv n).symm.toHomeomorph
  · intro w hw i φ hφ hcφ
    simpa only [Measure.restrict_univ] using
      ht.2.2 w hw i c φ ⟨hφ,hcφ,Set.subset_univ _⟩

end Yau.NodeProofs.P06Aux
