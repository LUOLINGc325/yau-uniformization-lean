import Yau.Proofs.Y01GermComposition

/-! Pointwise bounds for finite Fréchet jet composition. Only smooth germs
at zero and their actual derivative norms enter the estimate. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open scoped ContDiff

variable {n : ℕ}

theorem jetNorm_nonneg (f : ComplexVector n → ComplexVector n) (d : ℕ) : 0 ≤ jetNorm f d := by
  unfold jetNorm
  positivity

theorem derivative_norm_le_jetNorm (f : ComplexVector n → ComplexVector n) {d m : ℕ}
    (hm : m ≤ d) : ‖iteratedFDeriv ℂ m f 0‖ ≤ jetNorm f d := by
  unfold jetNorm
  exact Finset.single_le_sum (fun j hj => norm_nonneg (iteratedFDeriv ℂ j f 0))
    (Finset.mem_range.2 (by omega))

def partitionJetConstant (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (d + 1), (Fintype.card (OrderedFinpartition m) : ℝ)

theorem jetNorm_comp_bound {f g : ComplexVector n → ComplexVector n} {d : ℕ}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0) (hf0 : f 0 = 0) :
    jetNorm (g ∘ f) d ≤ partitionJetConstant d * jetNorm g d * (1 + jetNorm f d) ^ d := by
  have hB : 1 ≤ 1 + jetNorm f d := by linarith [jetNorm_nonneg f d]
  have hG : 0 ≤ jetNorm g d := jetNorm_nonneg g d
  have hterm (m : ℕ) (hm : m ≤ d) : ‖iteratedFDeriv ℂ m (g ∘ f) 0‖ ≤
      (Fintype.card (OrderedFinpartition m) : ℝ) * jetNorm g d * (1 + jetNorm f d) ^ d := by
    have hgF : ContDiffAt ℂ d g (f 0) := by simpa only [hf0] using hg
    rw [iteratedFDeriv_comp hgF hf (by exact_mod_cast hm), hf0]
    unfold FormalMultilinearSeries.taylorComp
    apply (norm_sum_le _ _).trans
    have hpart (c : OrderedFinpartition m) :
        ‖(ftaylorSeries ℂ g 0).compAlongOrderedFinpartition (ftaylorSeries ℂ f 0) c‖ ≤
          jetNorm g d * (1 + jetNorm f d) ^ d := by
      have houter : ‖iteratedFDeriv ℂ c.length g 0‖ ≤ jetNorm g d :=
        derivative_norm_le_jetNorm g (c.length_le.trans hm)
      have hprod : (∏ j : Fin c.length, ‖iteratedFDeriv ℂ (c.partSize j) f 0‖) ≤
          (1 + jetNorm f d) ^ d := by
        have hfirst : (∏ j : Fin c.length, ‖iteratedFDeriv ℂ (c.partSize j) f 0‖) ≤
            (1 + jetNorm f d) ^ c.length := by
          calc
            _ ≤ ∏ _j : Fin c.length, (1 + jetNorm f d) := by
              apply Finset.prod_le_prod₀
              · intro j hj
                exact norm_nonneg _
              · intro j hj
                exact (derivative_norm_le_jetNorm f ((c.partSize_le j).trans hm)).trans (by linarith)
            _ = _ := by simp
        exact hfirst.trans (pow_le_pow_right₀ hB (c.length_le.trans hm))
      exact (c.norm_compAlongOrderedFinpartition_le _ _).trans
        (mul_le_mul houter hprod (Finset.prod_nonneg fun j hj => norm_nonneg _) hG)
    calc
      _ ≤ ∑ c : OrderedFinpartition m, jetNorm g d * (1 + jetNorm f d) ^ d :=
        Finset.sum_le_sum (fun c hc => hpart c)
      _ = _ := by simp [mul_assoc]
  change (∑ m ∈ Finset.range (d + 1), ‖iteratedFDeriv ℂ m (g ∘ f) 0‖) ≤
    (∑ m ∈ Finset.range (d + 1), (Fintype.card (OrderedFinpartition m) : ℝ)) *
      jetNorm g d * (1 + jetNorm f d) ^ d
  calc
    _ ≤ ∑ m ∈ Finset.range (d + 1),
        (Fintype.card (OrderedFinpartition m) : ℝ) * jetNorm g d * (1 + jetNorm f d) ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      exact hterm m (by have := Finset.mem_range.1 hm; omega)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end Yau.Proofs.Y01Aux
