import Yau.Proofs.Y05FiniteJets

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment
open scoped ContDiff

section Composition

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] {d : ℕ}

theorem iteratedFDeriv_comp_congr_at
    {f f' : E → F} {g g' : F → G}
    (hf : ContDiffAt ℂ d f 0) (hf' : ContDiffAt ℂ d f' 0)
    (hg : ContDiffAt ℂ d g (f 0)) (hg' : ContDiffAt ℂ d g' (f' 0))
    (hff' : ∀ m ≤ d, iteratedFDeriv ℂ m f 0 = iteratedFDeriv ℂ m f' 0)
    (hgg' : ∀ m ≤ d, iteratedFDeriv ℂ m g (f 0) = iteratedFDeriv ℂ m g' (f' 0)) :
    ∀ m ≤ d, iteratedFDeriv ℂ m (g ∘ f) 0 = iteratedFDeriv ℂ m (g' ∘ f') 0 := by
  intro m hm
  rw [iteratedFDeriv_comp hg hf (by exact_mod_cast hm),
    iteratedFDeriv_comp hg' hf' (by exact_mod_cast hm)]
  exact finite_taylorComp_congr hff' hgg' hm

end Composition

variable {n d : ℕ}

theorem scalarJetEq_value {f g : ComplexVector n → ℂ} (h : ScalarJetEq f g d) : f 0 = g 0 := by
  have H := congrArg (fun L => L (fun i : Fin 0 => Fin.elim0 i)) (h 0 (Nat.zero_le d))
  simpa only [iteratedFDeriv_zero_apply] using H

theorem scalarJetEq_symm {f g : ComplexVector n → ℂ} (h : ScalarJetEq f g d) :
    ScalarJetEq g f d := fun m hm => (h m hm).symm

theorem scalarJetEq_trans {f g h : ComplexVector n → ℂ}
    (hfg : ScalarJetEq f g d) (hgh : ScalarJetEq g h d) : ScalarJetEq f h d :=
  fun m hm => (hfg m hm).trans (hgh m hm)

theorem scalarJetEq_add {f f' g g' : ComplexVector n → ℂ}
    (hf : ContDiffAt ℂ d f 0) (hf' : ContDiffAt ℂ d f' 0)
    (hg : ContDiffAt ℂ d g 0) (hg' : ContDiffAt ℂ d g' 0)
    (hff : ScalarJetEq f f' d) (hgg : ScalarJetEq g g' d) :
    ScalarJetEq (fun z => f z + g z) (fun z => f' z + g' z) d := by
  intro m hm
  change iteratedFDeriv ℂ m (f + g) 0 = iteratedFDeriv ℂ m (f' + g') 0
  rw [iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast hm))
    (hg.of_le (by exact_mod_cast hm)),
    iteratedFDeriv_add_apply (hf'.of_le (by exact_mod_cast hm))
    (hg'.of_le (by exact_mod_cast hm)), hff m hm, hgg m hm]

theorem scalarJetEq_mul {f f' g g' : ComplexVector n → ℂ}
    (hf : ContDiffAt ℂ d f 0) (hf' : ContDiffAt ℂ d f' 0)
    (hg : ContDiffAt ℂ d g 0) (hg' : ContDiffAt ℂ d g' 0)
    (hff : ScalarJetEq f f' d) (hgg : ScalarJetEq g g' d) :
    ScalarJetEq (fun z => f z * g z) (fun z => f' z * g' z) d := by
  have hpair0 : (f 0, g 0) = (f' 0, g' 0) := by
    rw [scalarJetEq_value hff, scalarJetEq_value hgg]
  have hmul : ContDiff ℂ d (fun p : ℂ × ℂ => p.1 * p.2) := contDiff_fst.mul contDiff_snd
  have hpair : ∀ m ≤ d, iteratedFDeriv ℂ m (fun z => (f z, g z)) 0 =
      iteratedFDeriv ℂ m (fun z => (f' z, g' z)) 0 := by
    intro m hm
    rw [iteratedFDeriv_prodMk hf hg (by exact_mod_cast hm),
      iteratedFDeriv_prodMk hf' hg' (by exact_mod_cast hm), hff m hm, hgg m hm]
  exact iteratedFDeriv_comp_congr_at (hf.prodMk hg) (hf'.prodMk hg')
    hmul.contDiffAt hmul.contDiffAt hpair
    (fun m hm => by simpa only [hpair0])

theorem scalarJetEq_exp {f g : ComplexVector n → ℂ}
    (hf : ContDiffAt ℂ d f 0) (hg : ContDiffAt ℂ d g 0) (h : ScalarJetEq f g d) :
    ScalarJetEq (fun z => Complex.exp (f z)) (fun z => Complex.exp (g z)) d := by
  have h0 := scalarJetEq_value h
  exact iteratedFDeriv_comp_congr_at hf hg
    (Complex.contDiff_exp.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (Complex.contDiff_exp.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt h
    (fun m hm => by simpa only [h0])

end Yau.Proofs.Y05Aux
