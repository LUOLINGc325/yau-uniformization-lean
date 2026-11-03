import Yau.Proofs.C05RicciTimeDerivative
import Yau.Proofs.C05RicciInverseTensor
import Yau.LeafProofs.L23MetricTimeCalculus

/-! Genuine time derivatives of inverse energies. Every summand in
the time derivative retains an undifferentiated scalar differential. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.C05Aux
open Yau Blueprint Yau.LeafProofs Set Filter
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem inverseMatrixEnergy_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℝ) (p : ℝ → ι → ℝ)
    (B : Matrix ι ι ℝ) (q : ι → ℝ) (t : ℝ)
    (hA : ∀ a b, HasDerivAt (fun s => A s a b) (B a b) t)
    (hp : ∀ a, HasDerivAt (fun s => p s a) (q a) t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * (p s ⬝ᵥ ((A s)⁻¹ *ᵥ p s)))
      ((1 / 2 : ℝ) * ∑ a : ι, ∑ b : ι,
        ((-((A t)⁻¹ * B * (A t)⁻¹)) a b * p t a * p t b +
          (A t)⁻¹ a b * q a * p t b + (A t)⁻¹ a b * p t a * q b)) t := by
  have hI := L23Aux.matrixInverse_hasDerivAt A B t hA hdet
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      ((hI a b).mul (hp a)).mul (hp b)))
  have hs := hd.const_mul (1 / 2 : ℝ)
  have he : (fun s => (1 / 2 : ℝ) * (p s ⬝ᵥ ((A s)⁻¹ *ᵥ p s))) =
      (fun s => (1 / 2 : ℝ) * ∑ a, ∑ b, (A s)⁻¹ a b * p s a * p s b) := by
    funext s
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he]
  convert hs using 1
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Pi.mul_apply, Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_apply]
  ring

theorem realRicci_hasDerivAt_scalar_levi (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (x : Pt X) {t : ℝ} (ht : 0 < t)
    (a b : RIdx n) :
    HasDerivAt (fun s => realRicciCoeff (h s) x (chartPt x x) a b)
      (2 * Yau.NodeProofs.G01Aux.rawReal (levi (scalarCurvature (h t)) x) a b) t := by
  have hR := ricci_hasDerivAt_scalar_levi o h U P ρ hf x ht a.1 b.1
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hR
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hR
  have hd : HasDerivAt
      (fun s => 2 * Yau.NodeProofs.G01Aux.rawReal (ricci (h s) x) a b)
      (2 * Yau.NodeProofs.G01Aux.rawReal (levi (scalarCurvature (h t)) x) a b) t := by
    by_cases hab : a.2 = b.2
    · simpa [Yau.NodeProofs.G01Aux.rawReal, hab, Function.comp_def] using hr.const_mul 2
    · by_cases ha : a.2 = 0
      · have hb : (0 : Fin 2) ≠ b.2 := fun he => hab (ha.trans he)
        simpa [Yau.NodeProofs.G01Aux.rawReal, hab, ha, hb, Function.comp_def] using (hi.neg).const_mul 2
      · simpa [Yau.NodeProofs.G01Aux.rawReal, hab, ha, Function.comp_def] using hi.const_mul 2
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hspos : 0 < s := by simpa only [mem_Ioi] using hs
  have hs0 : s ∈ Ici (0 : ℝ) := by
    change 0 ≤ s
    exact hspos.le
  exact Yau.NodeProofs.G04Aux.realRicciCoeff_center_raw (h s)
    (L23Aux.metricFamilySmooth_slice h hf.1.2.1 hs0) (hf.1.2.2.1 s hspos.le) x a b

end Yau.Proofs.C05Aux
