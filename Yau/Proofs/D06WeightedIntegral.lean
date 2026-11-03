import Yau.Proofs.D06HardyTraceShift

/-! The actual weighted Hardy integral. Linearity is proved in L² and hence
uses only almost-everywhere identities of the chosen trace representatives. -/

open scoped Matrix ComplexConjugate
open MeasureTheory

noncomputable section
namespace Yau.NodeProofs.D06Aux

variable {r : ℕ}

def hardyWeightedPoint (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (a b : HardySeq r) (t : HardyCircle) : ℂ :=
  ∑ i, ∑ j, star (hardyTraceLp a i t) * L t i j * hardyTraceLp b j t

def hardyWeightedInner (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (a b : HardySeq r) : ℂ :=
  ∑ i, ∑ j, ∫ t, star (hardyTraceLp a i t) * L t i j * hardyTraceLp b j t
    ∂hardyCircleMeasure

theorem hardyWeightedEntry_integrable
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
    (a b : HardySeq r) (i j : Fin r) :
    Integrable (fun t => star (hardyTraceLp a i t) * L t i j * hardyTraceLp b j t)
      hardyCircleMeasure := by
  have hfirst : MemLp (fun t => star (hardyTraceLp a i t) * L t i j) 2 hardyCircleMeasure :=
    (Lp.memLp (hardyTraceLp a i)).star.fun_mul (hL i j)
  have hprod : MemLp
      (fun t => star (hardyTraceLp a i t) * L t i j * hardyTraceLp b j t) 1
      hardyCircleMeasure := hfirst.fun_mul (Lp.memLp (hardyTraceLp b j))
  exact memLp_one_iff_integrable.mp hprod

theorem hardyWeightedPoint_integrable
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
    (a b : HardySeq r) : Integrable (hardyWeightedPoint L a b) hardyCircleMeasure := by
  exact integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => hardyWeightedEntry_integrable L hL a b i j

theorem hardyWeightedInner_eq_integral
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure) (a b : HardySeq r) :
    hardyWeightedInner L a b = ∫ t, hardyWeightedPoint L a b t ∂hardyCircleMeasure := by
  unfold hardyWeightedInner hardyWeightedPoint
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ fun j _ => hardyWeightedEntry_integrable L hL a b i j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hardyWeightedEntry_integrable L hL a b i j)]

theorem hardyWeightedInner_add_left
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ)
    (hL : ∀ i j, MemLp (fun t => L t i j) ⊤ hardyCircleMeasure)
    (a b c : HardySeq r) :
    hardyWeightedInner L (a + b) c = hardyWeightedInner L a c + hardyWeightedInner L b c := by
  unfold hardyWeightedInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_add (hardyWeightedEntry_integrable L hL a c i j)
    (hardyWeightedEntry_integrable L hL b c i j)]
  apply integral_congr_ae
  have h := Lp.coeFn_add (hardyTraceLp a i) (hardyTraceLp b i)
  rw [← hardyTraceLp_add] at h
  filter_upwards [h] with t ht
  simp only [Pi.add_apply] at ht
  rw [ht, star_add, add_mul, add_mul]

theorem hardyWeightedInner_smul_left
    (L : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (c : ℂ) (a b : HardySeq r) :
    hardyWeightedInner L (c • a) b = star c * hardyWeightedInner L a b := by
  unfold hardyWeightedInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_const_mul]
  apply integral_congr_ae
  have h := Lp.coeFn_smul c (hardyTraceLp a i)
  rw [← hardyTraceLp_smul] at h
  filter_upwards [h] with t ht
  rw [ht]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  ring

end Yau.NodeProofs.D06Aux
