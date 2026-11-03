import Yau.Proofs.P06CylinderRegularityMatrixBounds

/-! A scalar Caccioppoli estimate applied to every equation of a genuine
finite coupled parabolic system. Its forcing uses only the system's values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

variable {n : ℕ} {α : Type*} [Fintype α]

def systemFlux (a : Point n → Mat n)
    (d : α → α → Yau.RIdx n → Point n → ℝ) (U : Point n → α → ℝ)
    (r : α) (p : Point n) (i : Yau.RIdx n) : ℝ :=
  energyFlux a (spatialGradient (fun q => U q r)) p i + valueFlux d U r p i

theorem valueFlux_regular
    {d : α → α → Yau.RIdx n → Point n → ℝ} {U : Point n → α → ℝ}
    (hd : ∀ r c i, ContDiff ℝ ∞ (d r c i))
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r))
    (hcU : ∀ r, HasCompactSupport (fun p => U p r)) (r : α) (i : Yau.RIdx n) :
    ContDiff ℝ ∞ (fun p => valueFlux d U r p i) ∧
      HasCompactSupport (fun p => valueFlux d U r p i) := by
  exact ⟨ContDiff.sum fun c _ => (hd r c i).mul (hU c),
    compact_sum _ (fun c => (hcU c).mul_left)⟩

theorem valueSource_regular
    {e : α → α → Point n → ℝ} {U : Point n → α → ℝ}
    (he : ∀ r c, ContDiff ℝ ∞ (e r c))
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r))
    (hcU : ∀ r, HasCompactSupport (fun p => U p r)) (r : α) :
    ContDiff ℝ ∞ (valueSource e U r) ∧ HasCompactSupport (valueSource e U r) := by
  exact ⟨ContDiff.sum fun c _ => (he r c).mul (hU c),
    compact_sum _ (fun c => (hcU c).mul_left)⟩

theorem systemFlux_regular
    {a : Point n → Mat n} {d : α → α → Yau.RIdx n → Point n → ℝ}
    {U : Point n → α → ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun p => a p i j))
    (hd : ∀ r c i, ContDiff ℝ ∞ (d r c i))
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r))
    (hcU : ∀ r, HasCompactSupport (fun p => U p r)) (r : α) (i : Yau.RIdx n) :
    ContDiff ℝ ∞ (fun p => systemFlux a d U r p i) ∧
      HasCompactSupport (fun p => systemFlux a d U r p i) := by
  have hF := valueFlux_regular hd hU hcU r i
  refine ⟨(ContDiff.sum fun j _ => (ha i j).mul (gradient_contDiff (hU r) j)).add hF.1,
    (compact_sum _ (fun j =>
      ((hcU r).fderiv_apply ℝ (Yau.realVec j,0)).mul_left)).add hF.2⟩

theorem valueSquare_integrable {U : Point n → α → ℝ}
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r))
    (hcU : ∀ r, HasCompactSupport (fun p => U p r)) :
    Integrable (valueSquare U) volume := by
  apply integrable_finsetSum
  intro r _
  exact ((hU r).pow 2).continuous.integrable_of_hasCompactSupport (compact_square (hcU r))

/-- The numerical constant precedes every solution and all its derivatives.
The only equation assumed is the actual value-flux equation on the test's
support; its global energy identity is supplied by the computed residual. -/
theorem exists_system_gradient_constant (n : ℕ) (α : Type*) [Fintype α]
    (lam upper A D B M : ℝ) (hlam : 0 < lam)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : Set (Point n)) (a : Point n → Mat n)
      (d : α → α → Yau.RIdx n → Point n → ℝ)
      (e : α → α → Point n → ℝ) (η : Point n → ℝ)
      (U : Point n → α → ℝ),
    Elliptic Q a lam upper →
    (∀ p ∈ Q, ∀ i j, |a p i j| ≤ A) →
    (∀ i j, ContDiff ℝ ∞ (fun p => a p i j)) →
    (∀ r c i, ContDiff ℝ ∞ (d r c i)) →
    (∀ r c, ContDiff ℝ ∞ (e r c)) →
    (∀ r c i p, |d r c i p| ≤ D) → (∀ r c p, |e r c p| ≤ B) →
    Test Q η → (∀ p, |η p| ≤ 1) →
    (∀ p, |fderiv ℝ η p (0,1)| ≤ M) →
    (∀ p i, |fderiv ℝ η p (Yau.realVec i,0)| ≤ M) →
    (∀ r, ContDiff ℝ ∞ (fun p => U p r)) →
    (∀ r, HasCompactSupport (fun p => U p r)) →
    (∀ p ∈ tsupport η, ∀ r, fderiv ℝ (fun q => U q r) p (0,1) =
      (∑ i, fderiv ℝ (fun q => systemFlux a d U r q i) p (Yau.realVec i,0)) +
        valueSource e U r p) →
    (∫ p, η p^2 * ∑ r, ∑ i, (spatialGradient (fun q => U q r) p i)^2) ≤
      C * ∫ p, valueSquare U p := by
  classical
  obtain ⟨C0,hC0,hCacc⟩ := exists_caccioppoli_constant n lam upper A 0 M hlam hA
    (by norm_num) hM
  let K : ℝ := 1 + (Fintype.card α : ℝ) *
    ((Fintype.card (Yau.RIdx n) : ℝ) * D^2 + B^2)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨((Fintype.card α : ℝ)+1)*C0*K, by positivity, ?_⟩
  intro Q a d e η U hEll ha haSmooth hdSmooth heSmooth hd he hη hηB hTime hSpace hU hcU hPDE
  have hVal := valueSquare_integrable hU hcU
  have hValNonneg : 0 ≤ ∫ p, valueSquare U p := integral_nonneg fun p => valueSquare_nonneg U p
  have hEach (r : α) :
      (∫ p, η p^2 * ∑ i, (spatialGradient (fun q => U q r) p i)^2) ≤
        C0*K*(∫ p, valueSquare U p) := by
    let w : Point n → ℝ := fun p => U p r
    let P := systemFlux a d U r
    let F := fun p i => valueFlux d U r p i
    let f := valueSource e U r
    let R := divergenceResidual w P
    have hPS (i) := systemFlux_regular haSmooth hdSmooth hU hcU r i
    have hFS (i) := valueFlux_regular hdSmooth hU hcU r i
    have hfS := valueSource_regular heSmooth hU hcU r
    have hwL : MemLp w 2 volume := (hU r).continuous.memLp_of_hasCompactSupport (hcU r)
    have hHL (i) : MemLp (fun p => spatialGradient w p i) 2 volume :=
      (gradient_contDiff (hU r) i).continuous.memLp_of_hasCompactSupport
        ((hcU r).fderiv_apply ℝ (Yau.realVec i,0))
    have hPL (i) : MemLp (fun p => P p i) 2 volume :=
      (hPS i).1.continuous.memLp_of_hasCompactSupport (hPS i).2
    have hFL (i) : MemLp (fun p => F p i) 2 volume :=
      (hFS i).1.continuous.memLp_of_hasCompactSupport (hFS i).2
    have hfL : MemLp f 2 volume := hfS.1.continuous.memLp_of_hasCompactSupport hfS.2
    have hRL : MemLp R 2 volume :=
      (residual_contDiff (hU r) (fun i => (hPS i).1)).continuous.memLp_of_hasCompactSupport
        (residual_compact (hcU r) (fun i => (hPS i).2))
    have hSource : ∀ p ∈ tsupport η, R p = (∑ i, (0 : ℝ)*spatialGradient w p i)+f p := by
      intro p hp
      have h := hPDE p hp r
      simp only [zero_mul, Finset.sum_const_zero, zero_add]
      dsimp [R, divergenceResidual, w, P, f]
      linarith
    have hEstimate := hCacc Q a (fun _ _ => 0) η w f (spatialGradient w) P F R
      hEll ha (by intros; norm_num) hη hηB hTime hSpace hwL hHL hPL hRL hFL hfL
      (by intros; rfl) hSource
      (residual_energy_zero (hU r) (hcU r) (fun i => (hPS i).1)
        (fun i => (hPS i).2) hη.1 hη.2.1)
    have hForceInt : Integrable (fun p => (w p)^2 + (∑ i, (F p i)^2) + (f p)^2) volume := by
      have hw2 : Integrable (fun p => (w p)^2) volume := by
        exact hwL.integrable_sq
      have hF2 (i) : Integrable (fun p => (F p i)^2) volume := by
        exact (hFL i).integrable_sq
      have hf2 : Integrable (fun p => (f p)^2) volume := by
        exact hfL.integrable_sq
      exact (hw2.add (integrable_finsetSum _ (fun i _ => hF2 i))).add hf2
    have hBound := integral_mono hForceInt (hVal.const_mul K)
      (fun p => value_forcing_bound d e U hD hB hd he r p)
    rw [integral_const_mul] at hBound
    exact hEstimate.trans (by nlinarith)
  have hInt (r : α) : Integrable
      (fun p => η p^2 * ∑ i, (spatialGradient (fun q => U q r) p i)^2) volume := by
    have hS : ContDiff ℝ ∞ (fun p => ∑ i, (spatialGradient (fun q => U q r) p i)^2) :=
      ContDiff.sum fun i _ => (gradient_contDiff (hU r) i).pow 2
    exact ((hη.1.pow 2).mul hS).continuous.integrable_of_hasCompactSupport
      (compact_square hη.2.1).mul_right
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun r _ => by
    simpa only [Finset.mul_sum] using hInt r)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun r _ => hEach r)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum] at hs
  nlinarith [mul_nonneg hC0.le (mul_nonneg hK.le hValNonneg)]

end Yau.NodeProofs.P06Aux.CylinderReg
