import Yau.LeafProofs.L05ChuSharpRadius
import Yau.LeafProofs.L05DiniIteration

noncomputable section

open MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def chuOscillationSet {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (Q : Set (Point n)) (J : Point n → V) (r : ℝ) : Set ℝ :=
  {v | v=0 ∨ ∃ p ∈ Q, ∃ q ∈ Q, parabolicDistance p q ≤ r ∧ v=‖J p-J q‖}

def chuOscillation {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (Q : Set (Point n)) (J : Point n → V) (r : ℝ) : ℝ := sSup (chuOscillationSet Q J r)

theorem chuOscillationSet_nonempty {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (Q : Set (Point n)) (J : Point n → V) (r : ℝ) : (chuOscillationSet Q J r).Nonempty :=
  ⟨0,Or.inl rfl⟩

theorem chuOscillationSet_bdd {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {J : Point n → V} {M : ℝ} (hM : 0 ≤ M)
    (hJ : ∀ p ∈ Q, ‖J p‖ ≤ M) (r : ℝ) : BddAbove (chuOscillationSet Q J r) := by
  refine ⟨2*M,?_⟩
  rintro v (rfl | ⟨p,hp,q,hq,_,rfl⟩)
  · positivity
  · exact (norm_sub_le _ _).trans ((add_le_add (hJ p hp) (hJ q hq)).trans_eq (by ring))

theorem chuOscillation_nonneg {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {J : Point n → V} {M : ℝ} (hM : 0 ≤ M)
    (hJ : ∀ p ∈ Q, ‖J p‖ ≤ M) (r : ℝ) : 0 ≤ chuOscillation Q J r :=
  le_csSup (chuOscillationSet_bdd hM hJ r) (Or.inl rfl)

theorem chuOscillation_pair_le {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {J : Point n → V} {M r : ℝ} (hM : 0 ≤ M)
    (hJ : ∀ p ∈ Q, ‖J p‖ ≤ M) {p q : Point n} (hp : p ∈ Q) (hq : q ∈ Q)
    (hpq : parabolicDistance p q ≤ r) : ‖J p-J q‖ ≤ chuOscillation Q J r :=
  le_csSup (chuOscillationSet_bdd hM hJ r) (Or.inr ⟨p,hp,q,hq,hpq,rfl⟩)

theorem chuOscillation_le {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {J : Point n → V} {r c : ℝ} (hc : 0 ≤ c)
    (hJ : ∀ p ∈ Q, ∀ q ∈ Q, parabolicDistance p q ≤ r → ‖J p-J q‖ ≤ c) :
    chuOscillation Q J r ≤ c := by
  apply csSup_le (chuOscillationSet_nonempty Q J r)
  rintro v (rfl | ⟨p,hp,q,hq,hpq,rfl⟩)
  · exact hc
  · exact hJ p hp q hq hpq

theorem chuOscillation_monotone {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {J : Point n → V} {M : ℝ} (hM : 0 ≤ M)
    (hJ : ∀ p ∈ Q, ‖J p‖ ≤ M) : Monotone (chuOscillation Q J) := by
  intro r s hrs
  apply chuOscillation_le (chuOscillation_nonneg hM hJ s)
  intro p hp q hq hpq
  exact chuOscillation_pair_le hM hJ hp hq (hpq.trans hrs)

theorem chuOscillation_measurable {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {J : Point n → V} {M : ℝ} (hM : 0 ≤ M)
    (hJ : ∀ p ∈ Q, ‖J p‖ ≤ M) : Measurable (chuOscillation Q J) :=
  (chuOscillation_monotone hM hJ).measurable

theorem chuOscillation_powerBound {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {Q : Set (Point n)} {J : Point n → V} {eta M : ℝ} (he : 0 ≤ eta)
    (hJ : HolderBound eta Q J M) : powerBound eta (2*M) (chuOscillation Q J) := by
  intro r hr
  refine ⟨chuOscillation_nonneg hJ.1 hJ.2.1 r,?_⟩
  apply chuOscillation_le (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hJ.1)
    (Real.rpow_nonneg hr.1.le _))
  intro p hp q hq hpq
  have hw := holderWeight_le_twice_radius_power he hpq
  have hh := (hJ.2.2 p hp q hq).trans (mul_le_mul_of_nonneg_left hw hJ.1)
  nlinarith only [hh]

theorem chuOscillation_perturbation {n : ℕ} {V W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    {Q : Set (Point n)} {g : Point n → V} {J : Point n → W}
    {epsilon A gamma M r : ℝ} (heps : 0 ≤ epsilon) (hA : 0 ≤ A) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (hJ : ∀ p ∈ Q, ‖J p‖ ≤ M)
    (hpair : ∀ p ∈ Q, ∀ q ∈ Q, parabolicDistance p q ≤ r →
      ‖g p-g q‖ ≤ epsilon*‖J p-J q‖+A*r^gamma) :
    chuOscillation Q g r ≤ epsilon*chuOscillation Q J r+A*r^gamma := by
  have ho := chuOscillation_nonneg hM hJ r
  apply chuOscillation_le (add_nonneg (mul_nonneg heps ho) (mul_nonneg hA (Real.rpow_nonneg hr _)))
  intro p hp q hq hpq
  exact (hpair p hp q hq hpq).trans (add_le_add
    (mul_le_mul_of_nonneg_left (chuOscillation_pair_le hM hJ hp hq hpq) heps) le_rfl)

end Yau.LeafProofs.L05Aux
