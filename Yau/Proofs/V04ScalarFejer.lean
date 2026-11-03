import Yau.Proofs.V04FejerMultipliers
import Yau.Proofs.V03FourierParsevalCircle

/-! The actual finite Fejer multiplier has the exact circle Fourier
coefficients. Both retained attenuation and omitted modes remain visible. -/

open MeasureTheory AddCircle
open scoped Topology
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

variable {T : ℝ} [Fact (0 < T)]

def scalarFejer (u : AddCircle T → ℂ) (P : ℕ) (x : AddCircle T) : ℂ :=
  ∑ k ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    ((fejerMultiplier P k : ℂ) * fourierCoeff u k) * fourier k x

theorem scalarFejer_continuous (u : AddCircle T → ℂ) (P : ℕ) :
    Continuous (scalarFejer u P) := by
  unfold scalarFejer
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (fourier k).continuous

theorem scalarFejer_fourierCoeff (u : AddCircle T → ℂ) (P : ℕ) (l : ℤ) :
    fourierCoeff (scalarFejer u P) l = (fejerMultiplier P l : ℂ) * fourierCoeff u l := by
  let s := Finset.Icc (-(P : ℤ)) (P : ℤ)
  let f : ℤ → AddCircle T → ℂ := fun k x =>
    ((fejerMultiplier P k : ℂ) * fourierCoeff u k) * fourier k x
  have hsum := congrFun (fourierCoeff.sum s f (fun k _ =>
    (continuous_const.mul (fourier k).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))) l
  have hfeq : (∑ k ∈ s, f k) = scalarFejer u P := by
    funext x
    simp only [Finset.sum_apply, f, scalarFejer, s]
  rw [hfeq] at hsum
  calc
    _ = ∑ k ∈ s, ((fejerMultiplier P k : ℂ) * fourierCoeff u k) *
        fourierCoeff (fourier k) l := by
      simpa only [Finset.sum_apply, f, fourierCoeff.const_mul] using hsum
    _ = _ := by
      simp only [fourierCoeff_fourier, Pi.single_apply, mul_ite, mul_one, mul_zero]
      by_cases hl : l ∈ s
      · rw [Finset.sum_eq_single l]
        · simp
        · intro k hk hkl
          simp [hkl, Ne.symm hkl]
        · exact fun h => False.elim (h hl)
      · rw [Finset.sum_eq_zero (fun k hk => by
          have hkl : k ≠ l := fun h => hl (h ▸ hk)
          simp [hkl, Ne.symm hkl])]
        have hl' : l ∉ Finset.Icc (-(P : ℤ)) (P : ℤ) := hl
        rw [fejerMultiplier, if_neg hl']
        simp

theorem scalarFejer_sub_fourierCoeff {u : AddCircle T → ℂ} (hu : Continuous u)
    (P : ℕ) (k : ℤ) :
    fourierCoeff (fun x => scalarFejer u P x - u x) k =
      ((fejerMultiplier P k - 1 : ℝ) : ℂ) * fourierCoeff u k := by
  have hs := congrFun (fourierCoeff.add
    ((scalarFejer_continuous u P).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hu.neg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) k
  change fourierCoeff (fun x => scalarFejer u P x + -u x) k =
    fourierCoeff (scalarFejer u P) k + fourierCoeff (fun x => -u x) k at hs
  rw [show (fun x => -u x) = (fun x => (-1 : ℂ) * u x) by funext x; ring,
    fourierCoeff.const_mul, scalarFejer_fourierCoeff] at hs
  rw [Complex.ofReal_sub, Complex.ofReal_one]
  simpa only [sub_eq_add_neg] using hs.trans
    (show (fejerMultiplier P k : ℂ) * fourierCoeff u k + -1 * fourierCoeff u k =
      ((fejerMultiplier P k : ℂ) - 1) * fourierCoeff u k by ring)

end Yau.Blueprint.V04Proof
