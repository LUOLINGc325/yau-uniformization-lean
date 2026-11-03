import Yau.Proofs.P03AffineSchurParameters
import Yau.Proofs.P03BadParameterDimension

open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit affine row-solving chart, including the spatial variable
and exactly the free parameter columns. -/
def affineSchurChart (a : E → ι → ℂ) (pivot : ι) (b : E → Fin m → ℂ)
    (p : E × (Fin m → {l : ι // l ≠ pivot} → ℂ)) : Fin m → ι → ℂ :=
  affineSchurRows (a p.1) pivot (b p.1) p.2

theorem affineSchurChart_differentiableAt (a : E → ι → ℂ) (pivot : ι)
    (b : E → Fin m → ℂ)
    (p : E × (Fin m → {l : ι // l ≠ pivot} → ℂ))
    (ha : ∀ l, DifferentiableAt ℝ (fun x => a x l) p.1)
    (hb : ∀ i, DifferentiableAt ℝ (fun x => b x i) p.1)
    (hp : a p.1 pivot ≠ 0) : DifferentiableAt ℝ (affineSchurChart a pivot b) p := by
  have hfree (i : Fin m) (q : {l : ι // l ≠ pivot}) :
      DifferentiableAt ℝ
        (fun t : E × (Fin m → {l : ι // l ≠ pivot} → ℂ) => t.2 i q) p := by
    fun_prop
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro l
  by_cases hl : l = pivot
  · subst l
    simp only [affineSchurChart, affineSchurRows, ↓reduceDIte]
    change DifferentiableAt ℝ (fun q =>
      (b q.1 i - ∑ r : {l : ι // l ≠ pivot}, q.2 i r * a q.1 r.1) / a q.1 pivot) p
    simp only [div_eq_mul_inv]
    apply DifferentiableAt.mul
    · apply DifferentiableAt.sub ((hb i).comp p differentiableAt_fst)
      apply DifferentiableAt.fun_sum
      intro r _
      exact (hfree i r).mul ((ha r.1).comp p differentiableAt_fst)
    · exact ((ha pivot).comp p differentiableAt_fst).inv hp
  · change DifferentiableAt ℝ (fun q => affineSchurRows (a q.1) pivot (b q.1) q.2 i l) p
    simp only [affineSchurRows, dif_neg hl]
    exact hfree i ⟨l, hl⟩

theorem affineSchurChart_differentiableOn (a : E → ι → ℂ) (pivot : ι)
    (b : E → Fin m → ℂ) {U : Set E} (hU : IsOpen U)
    (ha : ∀ l, DifferentiableOn ℝ (fun x => a x l) U)
    (hb : ∀ i, DifferentiableOn ℝ (fun x => b x i) U) :
    DifferentiableOn ℝ (affineSchurChart a pivot b)
      {p | p.1 ∈ U ∧ a p.1 pivot ≠ 0} := by
  intro p hp
  exact (affineSchurChart_differentiableAt a pivot b p
    (fun l => (ha l p.1 hp.1).differentiableAt (hU.mem_nhds hp.1))
    (fun i => (hb i p.1 hp.1).differentiableAt (hU.mem_nhds hp.1)) hp.2).differentiableWithinAt

theorem affineSchurFreeRows_finrank (pivot : ι) :
    Module.finrank ℝ (Fin m → {l : ι // l ≠ pivot} → ℂ) =
      m * (Fintype.card ι - 1) * 2 := by
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Fintype.card_subtype_compl (fun l : ι => l = pivot)]
  simp only [Fintype.card_unique]
  ring

end Yau.NodeProofs.P03Aux
