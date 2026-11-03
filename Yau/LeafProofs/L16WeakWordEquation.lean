import Yau.LeafProofs.L16WeakWordSource

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def weakWordFlux {n : ℕ} (a : Point n → Mat n)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n))
    (p : Point n) (q : Yau.RIdx n) : ℝ :=
  energyFlux a (fun p j => U (j::w) p) p q+
    weakWordSource (fun j p => a p q j) U w p

def weakWordDrift {n : ℕ} (c : Point n → Yau.RIdx n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (p : Point n) : ℝ :=
  (∑ j, c p j*U (j::w) p)+weakWordSource (fun j p => c p j) U w p

theorem weakWordEquation_spatial_derivative {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (ha : ∀ q j, ContDiff ℝ ∞ (fun p => a p q j))
    (hca : ∀ q j, HasCompactSupport (fun p => a p q j))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (U : List (Yau.RIdx n) → Point n → ℝ) (k : ℕ)
    (hL2 : ∀ v, v.length ≤ k+2 → MemLp (U v) 2 (volume.restrict Q))
    (hWG : ∀ v, v.length ≤ k+1 → WeakGradientOn Q (U v) (fun p i => U (i::v) p))
    (w : List (Yau.RIdx n)) (hw : w.length ≤ k)
    (hEq : WeakDivergenceEvolutionOn Q (U w) (weakWordFlux a U w) (weakWordDrift c U w))
    (i : Yau.RIdx n) :
    WeakDivergenceEvolutionOn Q (U (i::w))
      (weakWordFlux a U (i::w)) (weakWordDrift c U (i::w)) := by
  let DP : Point n → Yau.RIdx n → Yau.RIdx n → ℝ := fun p q z =>
    (∑ j, (a p q j*U (z::j::w) p+U (j::w) p*fderiv ℝ (fun p => a p q j) p (Yau.realVec z,0)))+
      weakWordSourceGradient (fun j p => a p q j) U w p z
  let DR : Point n → Yau.RIdx n → ℝ := fun p z =>
    (∑ j, (c p j*U (z::j::w) p+U (j::w) p*fderiv ℝ (fun p => c p j) p (Yau.realVec z,0)))+
      weakWordSourceGradient (fun j p => c p j) U w p z
  have hPF (q : Yau.RIdx n) := weakGradientOn_weighted_finset_sum Finset.univ
    (fun j p => a p q j) (fun j => U (j::w)) (fun j p z => U (z::j::w) p)
    (fun j _ => hL2 (j::w) (by simp only [List.length_cons]; omega))
    (fun j _ z => hL2 (z::j::w) (by simp only [List.length_cons]; omega))
    (fun j _ => hWG (j::w) (by simp only [List.length_cons]; omega))
    (fun j _ => ha q j) (fun j _ => hca q j)
  have hSF (q : Yau.RIdx n) := weakWordSource_weakH1 hQ (fun j p => a p q j)
    (ha q) (hca q) U (k+1) (fun v hv => hL2 v (by omega)) hWG w (by omega)
  have hPR := weakGradientOn_weighted_finset_sum Finset.univ
    (fun j p => c p j) (fun j => U (j::w)) (fun j p z => U (z::j::w) p)
    (fun j _ => hL2 (j::w) (by simp only [List.length_cons]; omega))
    (fun j _ z => hL2 (z::j::w) (by simp only [List.length_cons]; omega))
    (fun j _ => hWG (j::w) (by simp only [List.length_cons]; omega))
    (fun j _ => hc j) (fun j _ => hcc j)
  have hSR := weakWordSource_weakH1 hQ (fun j p => c p j)
    hc hcc U (k+1) (fun v hv => hL2 v (by omega)) hWG w (by omega)
  have hWP (q : Yau.RIdx n) : WeakGradientOn Q (fun p => weakWordFlux a U w p q) (fun p z => DP p q z) :=
    weakGradientOn_add (hPF q).1 (hSF q).1 (hPF q).2.1 (hSF q).2.1 (hPF q).2.2 (hSF q).2.2
  have hWR : WeakGradientOn Q (weakWordDrift c U w) DR :=
    weakGradientOn_add hPR.1 hSR.1 hPR.2.1 hSR.2.1 hPR.2.2 hSR.2.2
  have hEqD := weakDivergenceEvolutionOn_spatial_derivative hEq (hWG w (by omega)) hWP hWR i
  have hSwap : ∀ᵐ p ∂volume.restrict Q, ∀ z j, U (z::j::w) p = U (j::z::w) p :=
    weak_second_spatial_derivatives_commute_ae hQ (hWG w (by omega))
      (fun z j => hL2 (z::j::w) (by simp only [List.length_cons]; omega))
      (fun j => hWG (j::w) (by simp only [List.length_cons]; omega))
  have hFluxEq (q : Yau.RIdx n) :
      (fun p => DP p q i) =ᵐ[volume.restrict Q] (fun p => weakWordFlux a U (i::w) p q) := by
    filter_upwards [hSwap] with p hp
    have hACom : (∑ j, a p q j*U (i::j::w) p) = ∑ j, a p q j*U (j::i::w) p :=
      Finset.sum_congr rfl (fun j _ => congrArg (fun z => a p q j*z) (hp i j))
    have hDCom : (∑ j, U (j::w) p*fderiv ℝ (fun p => a p q j) p (Yau.realVec i,0)) =
        ∑ j, fderiv ℝ (fun p => a p q j) p (Yau.realVec i,0)*U (j::w) p :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    dsimp only [DP,weakWordFlux,energyFlux]
    rw [weakWordSource_cons]
    simp only [weakWordCorrection,coefficientSpatialWord]
    rw [Finset.sum_add_distrib,hACom,hDCom]
    ring
  have hSourceEq : (fun p => DR p i) =ᵐ[volume.restrict Q] weakWordDrift c U (i::w) := by
    filter_upwards [hSwap] with p hp
    have hCCom : (∑ j, c p j*U (i::j::w) p) = ∑ j, c p j*U (j::i::w) p :=
      Finset.sum_congr rfl (fun j _ => congrArg (fun z => c p j*z) (hp i j))
    have hDCom : (∑ j, U (j::w) p*fderiv ℝ (fun p => c p j) p (Yau.realVec i,0)) =
        ∑ j, fderiv ℝ (fun p => c p j) p (Yau.realVec i,0)*U (j::w) p :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    dsimp only [DR,weakWordDrift]
    rw [weakWordSource_cons]
    simp only [weakWordCorrection,coefficientSpatialWord]
    rw [Finset.sum_add_distrib,hCCom,hDCom]
    ring
  exact weakDivergenceEvolutionOn_congr_ae hEqD
    (Filter.Eventually.of_forall (fun _ => rfl)) hFluxEq hSourceEq

end Yau.LeafProofs.L16Aux
