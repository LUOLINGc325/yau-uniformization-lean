import Yau.Proofs.F01ParabolicDilationLevi
import Yau.Proofs.F01ParabolicDilationTime
import Yau.Proofs.F01NormalizedPotentialSup
import Yau.Proofs.F01RelativeScalarSandwich
import Yau.Proofs.F01IotaDeterminant

/-! The initial scalar-coordinate adapter uses only the original local
background and the actual potential equation. Every transformed matrix,
clock value and C² extension is constructed from that same potential. -/
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def localNativePotentialMatrix (G : Space n → Matrix (Fin n) (Fin n) ℂ)
    (F : Point n → ℝ) (p : Point n) : Matrix (Fin n) (Fin n) ℂ :=
  G p.1 - (p.2 : ℂ) • backgroundRicci G p.1 + leviC (fun z => F (z,p.2)) p.1

def localNativePotentialClock (G : Space n → Matrix (Fin n) (Fin n) ℂ)
    (F : Point n → ℝ) (p : Point n) : ℝ :=
  Real.log (localNativePotentialMatrix G F p).det.re - Real.log (G p.1).det.re

def localNormalizedComplexBackground (G : Space n → Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℝ) (p : Point n) : Matrix (Fin n) (Fin n) ℂ :=
  G (ρ • p.1) + max p.2 0 • (-(ρ ^ 2) • backgroundRicci G (ρ • p.1))

theorem localNativePotentialMatrix_initial (G : Space n → Matrix (Fin n) (Fin n) ℂ)
    (F : Point n → ℝ) {O : Set (Space n)} (hO : IsOpen O)
    (hF0 : ∀ x ∈ O, F (x,0) = 0) {x : Space n} (hx : x ∈ O) :
    localNativePotentialMatrix G F (x,0) = G x := by
  have heq : (fun z => F (z,0)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hO.mem_nhds hx] with z hz using hF0 z hz
  simp only [localNativePotentialMatrix, Complex.ofReal_zero, zero_smul, sub_zero]
  rw [Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq heq, leviC_const, add_zero]

theorem localNativePotentialClock_initial (G : Space n → Matrix (Fin n) (Fin n) ℂ)
    (F : Point n → ℝ) {O : Set (Space n)} (hO : IsOpen O)
    (hF0 : ∀ x ∈ O, F (x,0) = 0) {x : Space n} (hx : x ∈ O) :
    localNativePotentialClock G F (x,0) = 0 := by
  rw [localNativePotentialClock, localNativePotentialMatrix_initial G F hO hF0 hx]
  exact sub_self _

theorem normalized_local_initial_complex_matrix
    (G : Space n → Matrix (Fin n) (Fin n) ℂ) (F : Point n → ℝ)
    {ρ r T : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hF : ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T))
    (hF0 : ∀ x ∈ ball 0 r, F (x,0) = 0)
    {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
    localNormalizedComplexBackground G ρ p +
      leviC (fun z => forwardZeroSpaceTime (parabolicRescalePotential ρ F) (z,p.2)) p.1 =
      localNativePotentialMatrix G F (parabolicDilation ρ (p.1,max p.2 0)) := by
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  by_cases ht : p.2 ≤ 0
  · have heq : (fun z => forwardZeroSpaceTime (parabolicRescalePotential ρ F) (z,p.2)) =
        fun _ => (0 : ℝ) := funext (fun _ => forwardZeroExtension_eq_of_nonpos _ ht)
    rw [heq, leviC_const]
    simp only [localNormalizedComplexBackground, max_eq_right ht, zero_smul, add_zero,
      parabolicDilation, mul_zero]
    exact (localNativePotentialMatrix_initial G F isOpen_ball hF0 hz).symm
  · have heq : (fun z => forwardZeroSpaceTime (parabolicRescalePotential ρ F) (z,p.2)) =
        fun z => parabolicRescalePotential ρ F (z,p.2) := by
      funext z
      simp only [forwardZeroSpaceTime, forwardZeroExtension, ht, ite_false]
    have hm := parabolicDilation_maps_positive hρ hρr hρT
      (show p ∈ ball 0 1 ×ˢ Icc 0 1 from ⟨hp.1,(lt_of_not_ge ht).le,hp.2.2⟩)
    rw [heq, parabolicRescalePotential_levi hρ.ne'
      (closed_slab_slice_jets hF isOpen_ball hm.1 hm.2).1]
    simp only [localNormalizedComplexBackground, localNativePotentialMatrix,
      parabolicDilation, max_eq_left (lt_of_not_ge ht).le, Complex.coe_smul]
    module

theorem normalized_local_initial_matrix
    (G : Space n → Matrix (Fin n) (Fin n) ℂ) (F : Point n → ℝ)
    {ρ r T : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hF : ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T))
    (hF0 : ∀ x ∈ ball 0 r, F (x,0) = 0)
    (hq : ContDiffOn ℝ ∞ (fun z => Real.log (G z).det.re) (ball 0 r))
    {p : Point n} (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
    clampedBackground (fun z => G (ρ • z)) p + complexHessianMap
      (hessian (forwardZeroSpaceTime (parabolicRescalePotential ρ F)) p) =
      iota (localNativePotentialMatrix G F (parabolicDilation ρ (p.1,max p.2 0))) := by
  have hz := spatialDilation_mem_ball hρ hρr hp.1
  rw [parabolicRescalePotential_clamped_matrix G hρ hρr hρT hF hp
    ((hq.contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp))]
  by_cases ht : p.2 ≤ 0
  · rw [if_pos ht, max_eq_right ht]
    simp only [parabolicDilation, mul_zero]
    rw [localNativePotentialMatrix_initial G F isOpen_ball hF0 hz]
  · rw [if_neg ht, max_eq_left (lt_of_not_ge ht).le]
    rfl

theorem normalized_local_initial_inputs
    (G : Space n → Matrix (Fin n) (Fin n) ℂ) (F : Point n → ℝ)
    {ρ r T M ell upper : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (hρT : ρ ^ 2 ≤ T)
    (hM : 0 ≤ M) (hell : 0 < ell)
    (hF : ContDiffOn ℝ ∞ F (ball 0 r ×ˢ Icc 0 T))
    (hF0 : ∀ x ∈ ball 0 r, F (x,0) = 0)
    (hq : ContDiffOn ℝ ∞ (fun z => Real.log (G z).det.re) (ball 0 r))
    (hPDE : ∀ x ∈ ball 0 r, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => F (x,s))
      (localNativePotentialClock G F (x,t)) (Icc 0 T) t)
    (hClock : ∀ p ∈ ball 0 r ×ˢ Icc 0 T, |localNativePotentialClock G F p| ≤ M)
    (hRange : ∀ p ∈ ball 0 r ×ˢ Icc 0 T,
      (localNativePotentialMatrix G F p - (ell : ℂ) • 1).PosSemidef ∧
      ((upper : ℂ) • 1 - localNativePotentialMatrix G F p).PosSemidef) :
    let V := forwardZeroSpaceTime (parabolicRescalePotential ρ F)
    let Q := cylinder (ball (0 : Space n) 1) (-1) 1
    let H := fun z => G (ρ • z)
    C2 Q V ∧ (∀ p ∈ Q, |V p| ≤ M) ∧ (∀ p ∈ Q, p.2 ≤ 0 → V p = 0) ∧
      (∀ p ∈ Q,
        (((clampedBackground H p + complexHessianMap (hessian V p) : Sym n) : Mat n) -
          ell • 1).PosSemidef ∧
        (upper • 1 - ((clampedBackground H p + complexHessianMap (hessian V p) : Sym n) : Mat n)).PosSemidef) ∧
      (∀ p ∈ Q, timeD Q V p -
        logDetReal (clampedBackground H p + complexHessianMap (hessian V p)) = backgroundSource H p) := by
  dsimp only
  have hP0 : ∀ x ∈ ball 0 r, localNativePotentialClock G F (x,0) = 0 :=
    fun x hx => localNativePotentialClock_initial G F isOpen_ball hF0 hx
  have hMap (p : Point n) (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
      parabolicDilation ρ (p.1,max p.2 0) ∈ ball 0 r ×ˢ Icc 0 T :=
    parabolicDilation_maps_positive hρ hρr hρT
      (show (p.1,max p.2 0) ∈ ball 0 1 ×ˢ Icc 0 1 from
        ⟨hp.1, le_max_right _ _, max_le hp.2.2 zero_le_one⟩)
  have hPos (p : Point n) (hp : p ∈ ball 0 r ×ˢ Icc 0 T) :
      (localNativePotentialMatrix G F p).PosDef := by
    have hh := (Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr hell)).add_posSemidef (hRange p hp).1
    simpa only [add_sub_cancel] using hh
  refine ⟨parabolicRescalePotential_zeroExtension_C2 hρ hρr hρT hF hF0 hP0 hPDE,
    normalized_zero_potential_sup_of_time_cap hρ hρr hρT hM hF0 hPDE
      (fun x hx t ht => hClock (x,t) ⟨hx,ht⟩),
    (fun p _ ht => forwardZeroExtension_eq_of_nonpos _ ht), ?_, ?_⟩
  · intro p hp
    rw [normalized_local_initial_matrix G F hρ hρr hρT hF hF0 hq hp]
    exact iota_scalar_matrix_sandwich (hRange _ (hMap p hp)).1 (hRange _ (hMap p hp)).2
  · intro p hp
    dsimp only [cylinder] at hp ⊢
    rw [zero_extended_parabolicRescalePotential_timeD hρ hρr hρT hF0 hP0 hPDE hp,
      normalized_local_initial_matrix G F hρ hρr hρT hF hF0 hq hp,
      logDetReal_iota_posDef _ (hPos _ (hMap p hp))]
    change (Real.log (localNativePotentialMatrix G F (parabolicDilation ρ (p.1,max p.2 0))).det.re -
      Real.log (G (ρ • p.1)).det.re) -
      Real.log (localNativePotentialMatrix G F (parabolicDilation ρ (p.1,max p.2 0))).det.re =
        -Real.log (G (ρ • p.1)).det.re
    ring

end Yau.NodeProofs.F01Aux
