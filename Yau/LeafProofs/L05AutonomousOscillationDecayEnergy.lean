import Yau.LeafProofs.L05AutonomousFiniteContractionExtrema
import Yau.LeafProofs.L05AutonomousPucciHolder
import Yau.LeafProofs.L05AutonomousOscillationDecayNumeric

noncomputable section
open Set
open scoped BigOperators
set_option maxHeartbeats 2200000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The energy is the sum of the actual range extrema on the genuine good set. -/
def autoJetOsc {n m : ℕ} (S : Set (Point n)) (w : Fin m → Point n → ℝ)
    (c : Space n) (R T : ℝ) : ℝ :=
  ∑ j, (finiteFieldSup (w j) (S ∩ autoClosed c R T) -
    finiteFieldInf (w j) (S ∩ autoClosed c R T))

theorem auto_jet_range_bounded {n : ℕ} {S Q : Set (Point n)} {B : ℝ}
    (v : Point n → ℝ) (hb : ∀ p ∈ S, |v p| ≤ B) :
    BddAbove (v '' (S ∩ Q)) ∧ BddBelow (v '' (S ∩ Q)) := by
  constructor
  · refine ⟨B, ?_⟩
    rintro z ⟨p,hp,rfl⟩
    exact (abs_le.mp (hb p hp.1)).2
  · refine ⟨-B, ?_⟩
    rintro z ⟨p,hp,rfl⟩
    exact (abs_le.mp (hb p hp.1)).1

/-- Every use of the conditional extrema is justified on a nonempty bounded range. -/
theorem auto_jet_scalar_extrema {n : ℕ} {S Q : Set (Point n)} {B : ℝ}
    (v : Point n → ℝ) (hb : ∀ p ∈ S, |v p| ≤ B) (hne : (S ∩ Q).Nonempty) :
    (∀ p ∈ S ∩ Q, finiteFieldInf v (S ∩ Q) ≤ v p ∧ v p ≤ finiteFieldSup v (S ∩ Q)) ∧
    -B ≤ finiteFieldInf v (S ∩ Q) ∧ finiteFieldSup v (S ∩ Q) ≤ B ∧
      finiteFieldInf v (S ∩ Q) ≤ finiteFieldSup v (S ∩ Q) := by
  obtain ⟨hU,hL⟩ := auto_jet_range_bounded v hb (Q := Q)
  have hv : ∀ p ∈ S ∩ Q, finiteFieldInf v (S ∩ Q) ≤ v p ∧
      v p ≤ finiteFieldSup v (S ∩ Q) := fun p hp =>
    ⟨csInf_le hL (mem_image_of_mem v hp), le_csSup hU (mem_image_of_mem v hp)⟩
  refine ⟨hv,?_,?_,?_⟩
  · exact le_csInf (hne.image v) (by
      rintro z ⟨p,hp,rfl⟩
      exact (abs_le.mp (hb p hp.1)).1)
  · exact csSup_le (hne.image v) (by
      rintro z ⟨p,hp,rfl⟩
      exact (abs_le.mp (hb p hp.1)).2)
  · obtain ⟨p,hp⟩ := hne
    exact (hv p hp).1.trans (hv p hp).2

theorem auto_jet_osc_nonneg {n m : ℕ} {S : Set (Point n)} {B : ℝ}
    (w : Fin m → Point n → ℝ) (hb : ∀ j, ∀ p ∈ S, |w j p| ≤ B)
    (c : Space n) (R T : ℝ) (hne : (S ∩ autoClosed c R T).Nonempty) :
    0 ≤ autoJetOsc S w c R T := by
  apply Finset.sum_nonneg
  intro j _
  exact sub_nonneg.mpr (auto_jet_scalar_extrema (w j) (hb j) hne).2.2.2

theorem auto_jet_osc_budget {n m : ℕ} {S : Set (Point n)} {B : ℝ}
    (w : Fin m → Point n → ℝ) (hb : ∀ j, ∀ p ∈ S, |w j p| ≤ B)
    (c : Space n) (R T : ℝ) (hne : (S ∩ autoClosed c R T).Nonempty) :
    autoJetOsc S w c R T ≤ 2*(m : ℝ)*B := by
  calc
    _ ≤ ∑ _j : Fin m, (2*B) := Finset.sum_le_sum (fun j _ => by
      have hx := auto_jet_scalar_extrema (w j) (hb j) hne
      linarith only [hx.2.1,hx.2.2.1])
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Both extrema vary monotonically on the actual nested good-set intersections. -/
theorem auto_jet_osc_mono {n m : ℕ} {S : Set (Point n)} {B r R : ℝ}
    (w : Fin m → Point n → ℝ) (hb : ∀ j, ∀ p ∈ S, |w j p| ≤ B)
    (c : Space n) (T : ℝ) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hne : (S ∩ autoClosed c r T).Nonempty) :
    autoJetOsc S w c r T ≤ autoJetOsc S w c R T := by
  apply Finset.sum_le_sum
  intro j _
  obtain ⟨hU,hL⟩ := auto_jet_range_bounded (w j) (hb j) (Q := autoClosed c R T)
  have hSub : S ∩ autoClosed c r T ⊆ S ∩ autoClosed c R T :=
    inter_subset_inter_right S (autoClosed_subset c hr hrR T)
  obtain ⟨_,_,_,_,hSup,hInf,_⟩ := finite_extrema_nested (w j) hne hSub hU hL
  linarith only [hSup,hInf]

/-- A scalar pair difference is bounded by the sum over the full indexed family, with repeats. -/
theorem auto_jet_osc_pair_le {n m : ℕ} {S : Set (Point n)} {B : ℝ}
    (w : Fin m → Point n → ℝ) (hb : ∀ j, ∀ p ∈ S, |w j p| ≤ B)
    (c : Space n) (R T : ℝ) (j : Fin m) {p q : Point n}
    (hp : p ∈ S ∩ autoClosed c R T) (hq : q ∈ S ∩ autoClosed c R T) :
    |w j p-w j q| ≤ autoJetOsc S w c R T := by
  have hne : (S ∩ autoClosed c R T).Nonempty := ⟨p,hp⟩
  have hx := auto_jet_scalar_extrema (w j) (hb j) hne
  have hpv := hx.1 p hp
  have hqv := hx.1 q hq
  have hpair : |w j p-w j q| ≤ finiteFieldSup (w j) (S ∩ autoClosed c R T) -
      finiteFieldInf (w j) (S ∩ autoClosed c R T) :=
    abs_le.mpr ⟨by linarith only [hpv.1,hqv.2], by linarith only [hpv.2,hqv.1]⟩
  apply hpair.trans
  exact Finset.single_le_sum (fun k _ =>
    sub_nonneg.mpr (auto_jet_scalar_extrema (w k) (hb k) hne).2.2.2) (Finset.mem_univ j)

end Yau.LeafProofs.L05AutonomousAux
