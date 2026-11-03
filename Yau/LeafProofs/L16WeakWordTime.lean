import Yau.LeafProofs.L16WeakWordBootstrap
import Yau.LeafProofs.L16WeakTimeCalculus

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def weakWordPairing {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (p : Point n) : ℝ :=
  (∑ j, g j p*U (j::w) p)+weakWordSource g U w p

def weakWordPairingGradient {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (p : Point n) (z : Yau.RIdx n) : ℝ :=
  (∑ j, (g j p*U (z::j::w) p+U (j::w) p*fderiv ℝ (g j) p (Yau.realVec z,0)))+
    weakWordSourceGradient g U w p z

theorem weakWordPairing_weakH1 {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (g : Yau.RIdx n → Point n → ℝ) (hg : ∀ j, ContDiff ℝ ∞ (g j))
    (hcg : ∀ j, HasCompactSupport (g j))
    (U : List (Yau.RIdx n) → Point n → ℝ) (k : ℕ)
    (hL2 : ∀ v, v.length ≤ k+2 → MemLp (U v) 2 (volume.restrict Q))
    (hWG : ∀ v, v.length ≤ k+1 → WeakGradientOn Q (U v) (fun p i => U (i::v) p))
    (w : List (Yau.RIdx n)) (hw : w.length ≤ k) :
    MemLp (weakWordPairing g U w) 2 (volume.restrict Q) ∧
      (∀ z, MemLp (fun p => weakWordPairingGradient g U w p z) 2 (volume.restrict Q)) ∧
      WeakGradientOn Q (weakWordPairing g U w) (weakWordPairingGradient g U w) := by
  have hP := weakGradientOn_weighted_finset_sum Finset.univ
    g (fun j => U (j::w)) (fun j p z => U (z::j::w) p)
    (fun j _ => hL2 (j::w) (by simp only [List.length_cons]; omega))
    (fun j _ z => hL2 (z::j::w) (by simp only [List.length_cons]; omega))
    (fun j _ => hWG (j::w) (by simp only [List.length_cons]; omega))
    (fun j _ => hg j) (fun j _ => hcg j)
  have hS := weakWordSource_weakH1 hQ g hg hcg U (k+1) (fun v hv => hL2 v (by omega))
    hWG w (by omega)
  have hVal : MemLp (weakWordPairing g U w) 2 (volume.restrict Q) := by
    convert! hP.1.add hS.1 using 1
  have hGrad (z : Yau.RIdx n) : MemLp (fun p => weakWordPairingGradient g U w p z) 2 (volume.restrict Q) := by
    convert! (hP.2.1 z).add (hS.2.1 z) using 1
  exact ⟨hVal,hGrad,weakGradientOn_add hP.1 hS.1 hP.2.1 hS.2.1 hP.2.2 hS.2.2⟩

def weakWordTime {n : ℕ} (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (p : Point n) : ℝ :=
  (∑ q, weakWordPairingGradient (fun j p => a p q j) U w p q)+weakWordDrift c U w p

theorem weakWordTime_weak_derivative {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (ha : ∀ q j, ContDiff ℝ ∞ (fun p => a p q j))
    (hca : ∀ q j, HasCompactSupport (fun p => a p q j))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (U : List (Yau.RIdx n) → Point n → ℝ) (k : ℕ)
    (hState : WeakSpatialWordState Q a c (k+1) U)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ k) :
    MemLp (weakWordTime a c U w) 2 (volume.restrict Q) ∧
      WeakDirectionalDerivativeOn Q (0,1) (U w) (weakWordTime a c U w) := by
  have hPF (q : Yau.RIdx n) := weakWordPairing_weakH1 hQ (fun j p => a p q j)
    (ha q) (hca q) U k (fun v hv => hState.1 v (by omega)) hState.2.1 w hw
  have hPR := weakWordPairing_weakH1 hQ (fun j p => c p j)
    hc hcc U k (fun v hv => hState.1 v (by omega)) hState.2.1 w hw
  have hWP (q : Yau.RIdx n) : WeakGradientOn Q (fun p => weakWordFlux a U w p q)
      (weakWordPairingGradient (fun j p => a p q j) U w) := (hPF q).2.2
  exact weakDivergenceEvolutionOn_timeDerivative (hState.2.2 w (by omega)) hWP
    (fun q => (hPF q).2.1 q) hPR.1

theorem weakWordTime_spatial_gradient {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (ha : ∀ q j, ContDiff ℝ ∞ (fun p => a p q j))
    (hca : ∀ q j, HasCompactSupport (fun p => a p q j))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (U : List (Yau.RIdx n) → Point n → ℝ) (k : ℕ)
    (hState : WeakSpatialWordState Q a c (k+2) U)
    (w : List (Yau.RIdx n)) (hw : w.length ≤ k) :
    MemLp (weakWordTime a c U w) 2 (volume.restrict Q) ∧
      (∀ i, MemLp (weakWordTime a c U (i::w)) 2 (volume.restrict Q)) ∧
      WeakGradientOn Q (weakWordTime a c U w) (fun p i => weakWordTime a c U (i::w) p) := by
  have hTime := weakWordTime_weak_derivative hQ a c ha hca hc hcc U (k+1) hState w (by omega)
  have hTimeI (i : Yau.RIdx n) := weakWordTime_weak_derivative hQ a c ha hca hc hcc U (k+1)
    hState (i::w) (by simp only [List.length_cons]; omega)
  exact ⟨hTime.1,fun i => (hTimeI i).1,weak_time_spatial_derivatives_commute
    (hState.2.1 w (by omega)) hTime.2 (fun i => (hTimeI i).2)⟩

end Yau.LeafProofs.L16Aux
