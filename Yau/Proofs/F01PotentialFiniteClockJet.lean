import Yau.Proofs.F01PotentialFiniteMatrixJet
import Yau.Proofs.F01FiniteLogDetSpatialJet

/-! The actual nonlinear potential clock equation has a smooth
finite-jet right-hand side on its positive matrix domain. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def potentialFiniteClockJet (k : ℕ)
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ)
    (p : Point n × FiniteTaylorJet (Space n) ℝ (k + 2)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => Space n) ℝ :=
  finiteLogDetSpatialJet k (potentialFiniteMatrixJet k S p) +
    iteratedFDeriv ℝ k (fun z => b (z, p.1.2)) p.1.1

def potentialFiniteClockDomain (k : ℕ)
    (S : Point n → Matrix (Fin n) (Fin n) ℂ) (W : Set (Point n)) :
    Set (Point n × FiniteTaylorJet (Space n) ℝ (k + 2)) :=
  {p | p.1 ∈ W ∧ 0 < ((potentialFiniteMatrixJet k S p ⟨0, by omega⟩).curry0).det.re}

theorem potentialFiniteClockJet_contDiffOn
    (k : ℕ) (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ)
    (W : Set (Point n))
    (hS : ∀ j : Fin (k + 1), ContDiffOn ℝ ∞
      (fun p : Point n => iteratedFDeriv ℝ j.val (fun z => S (z, p.2)) p.1) W)
    (hb : ContDiffOn ℝ ∞
      (fun p : Point n => iteratedFDeriv ℝ k (fun z => b (z, p.2)) p.1) W) :
    ContDiffOn ℝ ∞ (potentialFiniteClockJet k S b) (potentialFiniteClockDomain k S W) := by
  have hMatrix := (potentialFiniteMatrixJet_contDiffOn k S W hS).mono
    (show potentialFiniteClockDomain k S W ⊆ {p | p.1 ∈ W} from fun p hp => hp.1)
  have hLog := (finiteLogDetSpatialJet_contDiffOn (n := n) k).comp hMatrix
    (fun p hp => hp.2)
  have hBase : ContDiffOn ℝ ∞
      (fun p : Point n × FiniteTaylorJet (Space n) ℝ (k + 2) =>
        iteratedFDeriv ℝ k (fun z => b (z, p.1.2)) p.1.1)
      (potentialFiniteClockDomain k S W) :=
    hb.comp contDiffOn_fst (fun p hp => hp.1)
  exact hLog.add hBase

theorem potentialFiniteClockJet_native
    (k : ℕ) (S : Point n → Matrix (Fin n) (Fin n) ℂ) (b : Point n → ℝ)
    (q : Space n → ℝ) (p : Point n) {O : Set (Space n)}
    (hO : IsOpen O) (hp : p.1 ∈ O)
    (hS : ContDiffOn ℝ ∞ (fun z => S (z, p.2)) O)
    (hq : ContDiffOn ℝ ∞ q O) (hb : ContDiffOn ℝ ∞ (fun z => b (z, p.2)) O)
    (hPos : 0 < (S p + leviC q p.1).det.re) :
    potentialFiniteClockJet k S b (p, fun j => iteratedFDeriv ℝ j.val q p.1) =
      iteratedFDeriv ℝ k
        (fun z => Real.log (S (z, p.2) + leviC q z).det.re + b (z, p.2)) p.1 := by
  have hH : ContDiffAt ℝ ∞ (fun z => S (z, p.2) + leviC q z) p.1 :=
    (hS.add (native_levi_frobenius_contDiffOn hO hq)).contDiffAt (hO.mem_nhds hp)
  have hOuter : ContDiffAt ℝ ∞ (complexMatrixLogDet (n := n))
      (S p + leviC q p.1) :=
    complexMatrixLogDet_contDiffOn.contDiffAt
      (positive_real_determinant_domain_isOpen.mem_nhds hPos)
  have hLog : ContDiffAt ℝ ∞ (fun z => Real.log (S (z, p.2) + leviC q z).det.re) p.1 := by
    change ContDiffAt ℝ ∞ ((complexMatrixLogDet (n := n)) ∘
      (fun z => S (z, p.2) + leviC q z)) p.1
    exact hOuter.comp p.1 hH
  unfold potentialFiniteClockJet
  rw [potentialFiniteMatrixJet_native k S q p hO hp hS hq,
    finiteLogDetSpatialJet_native hH hPos k]
  exact (fun_iteratedFDeriv_add_apply (hLog.of_le (by simp))
    ((hb.contDiffAt (hO.mem_nhds hp)).of_le (by simp))).symm

end Yau.NodeProofs.F01Aux
