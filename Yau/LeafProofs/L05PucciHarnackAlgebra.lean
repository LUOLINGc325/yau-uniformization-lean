import Yau.LeafProofs.L05ABPAlgebra
import Yau.LeafProofs.L05PerronClassical

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def harnackPucciMinus {n : ℕ} (ell L : ℝ) (H : Sym n) : ℝ := -pucciPlus ell L (-H)

def harnackQminus (n : ℕ) : Set (Point n) :=
  Metric.ball 0 (1/4) ×ˢ Ioo (-3/4) (-1/2)

def harnackQplus (n : ℕ) : Set (Point n) :=
  Metric.ball 0 (1/4) ×ˢ Ioo (-1/4) 0

def harnackMu {n : ℕ} (E : Set (Point n)) : ℝ := ((volume : Measure (Point n)) E).toReal

def harnackSuper0 {n : ℕ} (ell L : ℝ) (u : Point n → ℝ) : Prop :=
  ContinuousOn u (unitClosed n) ∧ (∀ z ∈ unitClosed n, 0≤u z) ∧
    viscositySuper (unitOpen n) (fun H _ => harnackPucciMinus ell L H) (fun _ => 0) u

def harnackClosed {n : ℕ} (c : Space n) (R a T : ℝ) : Set (Point n) :=
  Metric.closedBall c R ×ˢ Icc a (a+T)

def harnackOpen {n : ℕ} (c : Space n) (R a T : ℝ) : Set (Point n) :=
  Metric.ball c R ×ˢ Ioo a (a+T)

def harnackBoundary {n : ℕ} (c : Space n) (R a T : ℝ) : Set (Point n) :=
  (Metric.closedBall c R ×ˢ ({a} : Set ℝ)) ∪ (Metric.sphere c R ×ˢ Icc a (a+T))

theorem harnack_tracePair_add {n : ℕ} (A H K : Sym n) :
    tracePair A (H+K)=tracePair A H+tracePair A K := by
  simp only [tracePair,AddSubgroup.coe_add,Matrix.mul_add,Matrix.trace_add]

theorem harnack_tracePair_smul {n : ℕ} (A H : Sym n) (a : ℝ) :
    tracePair A (a • H)=a*tracePair A H := by
  simp only [tracePair,selfAdjoint.val_smul,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]

theorem harnack_plus_add_le {n : ℕ} {ell L : ℝ} (hell : 0≤ell) (hL : ell≤L)
    (H K : Sym n) : pucciPlus ell L (H+K)≤pucciPlus ell L H+pucciPlus ell L K := by
  apply pucciPlus_le hL
  intro A hA
  rw [harnack_tracePair_add]
  exact add_le_add (tracePair_le_pucciPlus hell hA H) (tracePair_le_pucciPlus hell hA K)

theorem harnack_plus_smul_le {n : ℕ} {ell L a : ℝ} (hell : 0≤ell) (hL : ell≤L)
    (ha : 0≤a) (H : Sym n) : pucciPlus ell L (a • H)≤a*pucciPlus ell L H := by
  apply pucciPlus_le hL
  intro A hA
  rw [harnack_tracePair_smul]
  exact mul_le_mul_of_nonneg_left (tracePair_le_pucciPlus hell hA H) ha

theorem harnack_plus_smul {n : ℕ} {ell L a : ℝ} (hell : 0≤ell) (hL : ell≤L)
    (ha : 0≤a) (H : Sym n) : pucciPlus ell L (a • H)=a*pucciPlus ell L H := by
  rcases ha.eq_or_lt with ha0 | haPos
  · rw [← ha0,zero_smul,zero_mul,pucciPlus_zero hell hL]
  · have hInv := harnack_plus_smul_le hell hL (inv_nonneg.mpr ha) (a • H)
    rw [inv_smul_smul₀ haPos.ne'] at hInv
    have hLower := mul_le_mul_of_nonneg_left hInv ha
    rw [← mul_assoc,mul_inv_cancel₀ haPos.ne',one_mul] at hLower
    exact le_antisymm (harnack_plus_smul_le hell hL ha H) hLower

theorem harnack_minus_smul {n : ℕ} {ell L a : ℝ} (hell : 0≤ell) (hL : ell≤L)
    (ha : 0≤a) (H : Sym n) : harnackPucciMinus ell L (a • H)=a*harnackPucciMinus ell L H := by
  unfold harnackPucciMinus
  rw [← smul_neg,harnack_plus_smul hell hL ha]
  ring

theorem harnack_minus_sub {n : ℕ} {ell L : ℝ} (hell : 0≤ell) (hL : ell≤L)
    (A B : Sym n) : harnackPucciMinus ell L A-pucciPlus ell L B≤
      harnackPucciMinus ell L (A-B) := by
  have h := harnack_plus_add_le hell hL (-A) B
  have he : -(A-B)=-A+B := by abel
  unfold harnackPucciMinus
  rw [he]
  linarith

theorem harnack_minus_psd_difference {n : ℕ} {ell L : ℝ} (_hell : 0≤ell) (hL : ell≤L)
    {P N : Sym n} (hP : (P : Mat n).PosSemidef) (hN : (N : Mat n).PosSemidef) :
    ell*Matrix.trace (P : Mat n)-L*Matrix.trace (N : Mat n)≤harnackPucciMinus ell L (P-N) := by
  have hBound : pucciPlus ell L (-(P-N))≤L*Matrix.trace (N : Mat n)-ell*Matrix.trace (P : Mat n) := by
    apply pucciPlus_le hL
    intro A hA
    have hLower := posSemidef_trace_mul_nonneg hA.1 hP
    have hUpper := posSemidef_trace_mul_nonneg hA.2 hN
    simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,
      Matrix.trace_smul,smul_eq_mul] at hLower hUpper
    simp only [tracePair,AddSubgroup.coe_neg,AddSubgroup.coe_sub,Matrix.mul_neg,
      Matrix.mul_sub,Matrix.trace_neg,Matrix.trace_sub]
    linarith
  unfold harnackPucciMinus
  linarith

theorem harnack_plus_nonneg_of_psd {n : ℕ} {ell L : ℝ} (hell : 0≤ell) (hL : ell≤L)
    {H : Sym n} (hH : (H : Mat n).PosSemidef) : 0≤pucciPlus ell L H := by
  obtain ⟨A,hA⟩ := slopeSet_nonempty n hL
  have ht := posSemidef_trace_mul_nonneg (slopeSet_posSemidef hell hA) hH
  exact ht.trans (tracePair_le_pucciPlus hell hA H)

theorem harnack_plus_mono {n : ℕ} {ell L : ℝ} (hell : 0≤ell) (hL : ell≤L)
    {H K : Sym n} (hH : ((K-H : Sym n) : Mat n).PosSemidef) :
    pucciPlus ell L H≤pucciPlus ell L K := by
  apply pucciPlus_le hL
  intro A hA
  have ht := posSemidef_trace_mul_nonneg (slopeSet_posSemidef hell hA) hH
  have hPair := tracePair_sub A K H
  change 0≤tracePair A (K-H) at ht
  have hk := tracePair_le_pucciPlus hell hA K
  linarith

theorem harnack_minus_mono {n : ℕ} {ell L : ℝ} (hell : 0≤ell) (hL : ell≤L)
    {H K : Sym n} (hH : ((K-H : Sym n) : Mat n).PosSemidef) :
    harnackPucciMinus ell L H≤harnackPucciMinus ell L K := by
  have hNeg : (((-H)-(-K) : Sym n) : Mat n).PosSemidef := by
    have he : (-H)-(-K)=K-H := by abel
    rwa [he]
  have h := harnack_plus_mono hell hL hNeg
  unfold harnackPucciMinus
  linarith

theorem harnack_smooth_minus_super_sub {n : ℕ} {ell L : ℝ} {Q : Set (Point n)}
    (hell : 0≤ell) (hL : ell≤L) {u Phi G : Point n → ℝ}
    (hPhi : ∀ z∈Q, ContDiffAt ℝ 2 Phi z)
    (hSuper : viscositySuper Q (fun H _ => harnackPucciMinus ell L H) (fun _ => 0) u)
    (hRes : ∀ z∈Q, timeD univ Phi z-harnackPucciMinus ell L (hessian Phi z)≤G z) :
    viscositySub Q (fun H _ => pucciPlus ell L H) G (fun z => Phi z-u z) := by
  intro p hp psi hpsi ht
  have hTest : touchBelow (fun z => Phi z-psi z) u p := by
    refine ⟨?_,?_⟩
    · change Phi p-psi p=u p
      linarith [ht.1]
    · filter_upwards [ht.2] with z hz
      linarith
  have hS := hSuper p hp _ ((hPhi p hp).sub hpsi) hTest
  change 0≤timeD univ (fun z => Phi z-psi z) p-
    harnackPucciMinus ell L (hessian (fun z => Phi z-psi z) p) at hS
  rw [perron_timeD_sub (hPhi p hp) hpsi,perron_hessian_sub (hPhi p hp) hpsi] at hS
  have hDiff := harnack_minus_sub hell hL (hessian Phi p) (hessian psi p)
  have hR := hRes p hp
  linarith

theorem harnack_time_affine_jets {n : ℕ} (p : Point n) :
    timeD univ (fun z : Point n => z.2+1) p=1 ∧
      hessian (fun z : Point n => z.2+1) p=0 := by
  constructor
  · simp [timeD]
  · simp [hessian,spatialDD]
    exact (selfAdjointPart ℝ).map_zero

theorem harnack_homogenize {n : ℕ} {ell L : ℝ} {v : Point n → ℝ}
    (hv : ContinuousOn v (unitClosed n)) (hnonneg : ∀ z∈unitClosed n, 0≤v z)
    (hSuper : viscositySuper (unitOpen n)
      (fun H _ => harnackPucciMinus ell L H) (fun _ => -1) v) :
    harnackSuper0 ell L (fun z => v z+z.2+1) := by
  refine ⟨(hv.add continuous_snd.continuousOn).add_const 1,?_,?_⟩
  · intro z hz
    have h := hnonneg z hz
    have ht := hz.2.1
    linarith
  · intro p hp psi hpsi ht
    have hAff : ContDiffAt ℝ 2 (fun z : Point n => z.2+1) p := by fun_prop
    have hTest : touchBelow (fun z => psi z-(z.2+1)) v p := by
      refine ⟨?_,?_⟩
      · change psi p-(p.2+1)=v p
        linarith [ht.1]
      · filter_upwards [ht.2] with z hz
        linarith
    have h := hSuper p hp _ (hpsi.sub hAff) hTest
    change -1≤timeD univ (fun z => psi z-(z.2+1)) p-
      harnackPucciMinus ell L (hessian (fun z => psi z-(z.2+1)) p) at h
    rw [perron_timeD_sub hpsi hAff,perron_hessian_sub hpsi hAff,
      (harnack_time_affine_jets p).1,(harnack_time_affine_jets p).2,sub_zero] at h
    linarith

end Yau.LeafProofs.L05Aux
