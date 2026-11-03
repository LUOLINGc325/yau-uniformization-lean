import Yau.LeafProofs.L10InteriorExact
import Yau.LeafProofs.L09

/-! Interior Sobolev control by finitely many actual powers of the same elliptic operator. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau LeafCandidates LeafProofs
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

theorem elliptic_power_sobolev_bound (n : ℕ) (hn : 0 < n) (N : ℕ)
    (r R ell A : ℝ) (hr : 0 < r) (hrR : r < R) (hell : 0 < ell) (hA : 0 < A) :
    ∃ C : ℝ,0 < C ∧
      ∀ (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
        (b : ComplexVector n → RIdx n → ℝ),
      (∀ i j,ContDiffOn ℝ ∞ (fun z => a z i j) (Metric.ball 0 R)) →
      (∀ i,ContDiffOn ℝ ∞ (fun z => b z i) (Metric.ball 0 R)) →
      (∀ z ∈ Metric.ball 0 R,∀ v : RIdx n → ℝ,
        ell * ∑ i,(v i)^2 ≤ ∑ i,∑ j,a z i j*v i*v j) →
      (∀ k ≤ 2*N+1,∀ z ∈ Metric.ball 0 R,∀ i j,
        ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A ∧
        ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A) →
      ∀ u : ComplexVector n → ℂ,
      (∀ p ≤ N,ContDiffOn ℝ ∞ ((ellipticOp a b)^[p] u) (Metric.ball 0 R)) →
      (∀ p ≤ N,∀ j ≤ 2*(N-p),IntegrableOn
        (fun z => ‖iteratedFDeriv ℝ j ((ellipticOp a b)^[p] u) z‖^2)
        (Metric.ball 0 R) (lebesgueC n)) →
      sobolevNormSq (Metric.ball 0 r) u (2*N) ≤
        C * ∑ p ∈ Finset.range (N+1),
          ∫ z in Metric.ball 0 R,‖((ellipticOp a b)^[p] u) z‖^2 ∂lebesgueC n := by
  induction N generalizing r R with
  | zero =>
    refine ⟨1,one_pos,?_⟩
    intro a b _ha _hb _hEll _hBound u _hu hi
    simp only [Nat.mul_zero,Nat.zero_add,Finset.sum_range_one,Function.iterate_zero_apply,one_mul]
    rw [sobolevNormSq_zero]
    exact setIntegral_mono_set (by simpa only [Function.iterate_zero_apply,norm_iteratedFDeriv_zero] using hi 0 (by omega) 0 (by omega))
      (ae_of_all _ (fun z => sq_nonneg ‖u z‖))
      (ae_of_all _ (fun z hz => Metric.ball_subset_ball hrR.le hz))
  | succ N ih =>
    let rho := (r+R)/2
    have hrho : 0 < rho := by dsimp [rho];linarith
    have hr_rho : r < rho := by dsimp [rho];linarith
    have hrho_R : rho < R := by dsimp [rho];linarith
    obtain ⟨C0,hC0,hStep⟩ := elliptic_interior_energy_estimate n hn (2*N) r rho ell A
      hr hr_rho hell hA
    obtain ⟨C1,hC1,hPower⟩ := ih rho R hrho hrho_R
    refine ⟨C0*(C1+1),by positivity,?_⟩
    intro a b ha hb hEll hBound u hu hi
    let L := ellipticOp a b
    let Q : ℕ → ℝ := fun p => ∫ z in Metric.ball 0 R,‖(L^[p] u) z‖^2 ∂lebesgueC n
    have hSub : Metric.ball (0 : ComplexVector n) rho ⊆ Metric.ball 0 R :=
      Metric.ball_subset_ball hrho_R.le
    have hLu : ∀ p,L^[p] (L u)=L^[p+1] u := fun p =>
      (Function.iterate_succ_apply L p u).symm
    have hShift := hPower a b ha hb hEll
      (fun k hk z hz i j => hBound k (by omega) z hz i j) (L u)
      (fun p hp => by rw [hLu];exact hu (p+1) (by omega))
      (fun p hp j hj => by rw [hLu];exact hi (p+1) (by omega) j (by omega))
    have hStep' := hStep a b (fun i j => (ha i j).mono hSub)
      (fun i => (hb i).mono hSub) (fun z hz => hEll z (hSub hz))
      (fun k hk z hz i j => hBound k (by omega) z (hSub hz) i j)
      u ((hu 0 (by omega)).mono hSub)
      (fun j hj => (hi 0 (by omega) j (by omega)).mono_set hSub)
      (fun j hj => (hi 1 (by omega) j (by omega)).mono_set hSub)
    have hZero : sobolevNormSq (Metric.ball 0 rho) u 0 ≤ Q 0 := by
      rw [sobolevNormSq_zero]
      exact setIntegral_mono_set (by simpa only [Function.iterate_zero_apply,norm_iteratedFDeriv_zero] using hi 0 (by omega) 0 (by omega))
        (ae_of_all _ (fun z => sq_nonneg ‖u z‖)) (ae_of_all _ (fun z hz => hSub hz))
    have hSum : (∑ p ∈ Finset.range (N+1),
        ∫ z in Metric.ball 0 R,‖(L^[p] (L u)) z‖^2 ∂lebesgueC n)=
        ∑ p ∈ Finset.range (N+1),Q (p+1) := by simp only [hLu,Q]
    change sobolevNormSq (Metric.ball 0 rho) (L u) (2*N) ≤ _ at hShift
    rw [hSum] at hShift
    have hQ0 : 0 ≤ Q 0 := integral_nonneg (fun _ => sq_nonneg _)
    have hQS : 0 ≤ ∑ p ∈ Finset.range (N+1),Q (p+1) :=
      Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))
    have hFull : (∑ p ∈ Finset.range (N+1+1),Q p)=
        Q 0+∑ p ∈ Finset.range (N+1),Q (p+1) := by
      simpa only [add_comm] using Finset.sum_range_succ' Q (N+1)
    change sobolevNormSq (Metric.ball 0 r) u (2*(N+1)) ≤
      C0*(C1+1)*∑ p ∈ Finset.range (N+1+1),Q p
    rw [hFull]
    have hOrder : 2*(N+1)=2*N+2 := by omega
    rw [hOrder]
    calc
      _ ≤ C0*(sobolevNormSq (Metric.ball 0 rho) u 0+
          sobolevNormSq (Metric.ball 0 rho) (L u) (2*N)) := hStep'
      _ ≤ C0*(Q 0+C1*∑ p ∈ Finset.range (N+1),Q (p+1)) :=
        mul_le_mul_of_nonneg_left (add_le_add hZero hShift) hC0.le
      _ ≤ _ := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hC0.le
        nlinarith [mul_nonneg hC1.le hQ0]

theorem elliptic_power_tensor_bound (n : ℕ) (hn : 0 < n) (m N : ℕ)
    (hOrder : m+n < 2*N) (r R ell A : ℝ)
    (hr : 0 < r) (hrR : r < R) (hell : 0 < ell) (hA : 0 < A) :
    ∃ C : ℝ,0 < C ∧
      ∀ (a : ComplexVector n → Matrix (RIdx n) (RIdx n) ℝ)
        (b : ComplexVector n → RIdx n → ℝ),
      (∀ i j,ContDiffOn ℝ ∞ (fun z => a z i j) (Metric.ball 0 R)) →
      (∀ i,ContDiffOn ℝ ∞ (fun z => b z i) (Metric.ball 0 R)) →
      (∀ z ∈ Metric.ball 0 R,∀ v : RIdx n → ℝ,
        ell * ∑ i,(v i)^2 ≤ ∑ i,∑ j,a z i j*v i*v j) →
      (∀ k ≤ 2*N+1,∀ z ∈ Metric.ball 0 R,∀ i j,
        ‖iteratedFDeriv ℝ k (fun w => a w i j) z‖ ≤ A ∧
        ‖iteratedFDeriv ℝ k (fun w => b w i) z‖ ≤ A) →
      ∀ u : ComplexVector n → ℂ,
      (∀ p ≤ N,ContDiffOn ℝ ∞ ((ellipticOp a b)^[p] u) (Metric.ball 0 R)) →
      (∀ p ≤ N,∀ j ≤ 2*(N-p),IntegrableOn
        (fun z => ‖iteratedFDeriv ℝ j ((ellipticOp a b)^[p] u) z‖^2)
        (Metric.ball 0 R) (lebesgueC n)) →
      ∀ z ∈ Metric.ball 0 r,‖iteratedFDeriv ℝ m u z‖ ≤
        C * Real.sqrt (∑ p ∈ Finset.range (N+1),
          ∫ w in Metric.ball 0 R,‖((ellipticOp a b)^[p] u) w‖^2 ∂lebesgueC n) := by
  let rho := (r+R)/2
  have hrho : 0 < rho := by dsimp [rho];linarith
  have hr_rho : r < rho := by dsimp [rho];linarith
  have hrho_R : rho < R := by dsimp [rho];linarith
  obtain ⟨CE,hCE,hEmbed⟩ := interiorSobolevEmbedding n m (2*N) hOrder r rho hr hr_rho
  obtain ⟨CP,hCP,hPower⟩ := elliptic_power_sobolev_bound n hn N rho R ell A hrho hrho_R hell hA
  refine ⟨CE*Real.sqrt CP,mul_pos hCE (Real.sqrt_pos.mpr hCP),?_⟩
  intro a b ha hb hEll hBound u hu hi z hz
  have hSub : Metric.ball (0 : ComplexVector n) rho ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball hrho_R.le
  have hB := hPower a b ha hb hEll hBound u hu hi
  have hE := hEmbed u ((hu 0 (by omega)).mono hSub)
    (fun j hj => (hi 0 (by omega) j (by omega)).mono_set hSub) z hz
  exact hE.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) hCE.le).trans_eq
    (by rw [Real.sqrt_mul hCP.le];ring))

end Yau.Proofs.F03Aux
