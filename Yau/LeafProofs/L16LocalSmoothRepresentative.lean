import Yau.LeafProofs.L16LocalWeakWordJets
import Yau.LeafProofs.L16JetExpressionIteration
import Yau.LeafProofs.L16ParabolicRegularity

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem localEnergy_homogeneous_local_smooth_representative {n : ℕ}
    {O : Set (Space n)} {l r lam upper : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (O ×ˢ Set.Ioo l r) a b)
    (hEll : Elliptic (O ×ˢ Set.Ioo l r) a lam upper)
    {u : Point n → ℝ} {G : Point n → Yau.RIdx n → ℝ}
    (hE : LocalEnergy O (Set.Ioo l r) u G)
    (hEq : WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G)
    {V : Set (Point n)} (hV : IsOpen V) (hVC : IsCompact (closure V))
    (hVQ : closure V ⊆ O ×ˢ Set.Ioo l r) :
    ∃ v : Point n → ℝ, ContDiff ℝ ∞ v ∧ u =ᵐ[volume.restrict V] v := by
  have hQ : IsOpen (O ×ˢ Set.Ioo l r) := hO.prod isOpen_Ioo
  obtain ⟨W,hW,hVW,hWQ,hWC⟩ := exists_open_between_and_isCompact_closure hVC hQ hVQ
  obtain ⟨Q0,hQ0,hWQ0,hQ0Q,hQ0C⟩ := exists_open_between_and_isCompact_closure hWC hQ hWQ
  obtain ⟨A,c,C,hC,hA,hcA,hc,hAVal,hADq,hCVal,hCDq,hEllQ0,hBase⟩ :=
    localEnergy_homogeneous_extended_base_state hO hSmooth hEll hE hEq hQ0 hQ0C hQ0Q
  obtain ⟨η,hη,hNear⟩ := exists_test_eq_one_near_compact hW hVC hVW
  have haEntry (q j : Yau.RIdx n) : ContDiff ℝ ∞ (fun p => A p q j) :=
    (matrixEntryCLM q j).contDiff.comp hA
  have hcaEntry (q j : Yau.RIdx n) : HasCompactSupport (fun p => A p q j) :=
    hcA.comp_left (g := fun M : Mat n => M q j) (by simp)
  have hJets : ∀ N : ℕ, ∃ J : List (ParabolicJointIdx n) → Point n → ℝ,
      FiniteParabolicWeakJet N (fun p => η p*u p) J := by
    intro N
    obtain ⟨U,hU0,hState⟩ := exists_finite_weakSpatialWordState hQ0 hC.le hEllQ0 hA hcA
      (fun j => (hc j).1) (fun j => (hc j).2) hAVal hCVal hADq hCDq
      (initialWeakWordFamily u G) hBase (2*N+2) W hW hWC hWQ0
    exact finiteParabolicWeakJet_of_spatial_word_state hW A c haEntry hcaEntry
      (fun j => (hc j).1) (fun j => (hc j).2) hη N U (hU0 [] (by simp)) hState
  obtain ⟨v,hv,hAE⟩ := smooth_representative_of_finite_parabolic_weak_jets hJets
  have hAEV : v =ᵐ[volume.restrict V] (fun p => η p*u p) := ae_restrict_of_ae hAE
  refine ⟨v,hv,?_⟩
  filter_upwards [hAEV,ae_restrict_mem hV.measurableSet] with p hp hpV
  have hOne : η p = 1 := (hNear p (subset_closure hpV)).eq_of_nhds
  rw [hOne,one_mul] at hp
  exact hp.symm

end Yau.LeafProofs.L16Aux
