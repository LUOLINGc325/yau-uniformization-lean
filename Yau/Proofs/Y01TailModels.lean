import Yau.Proofs.Y01GridModels
import Yau.Proofs.Y01GermConjugacy
import Yau.Proofs.Y01TailArithmetic

/-! PolynomialModels transfers to a literal later canonical grid by exact
restriction of the already constructed models, with its original Cd/Dstar. -/

noncomputable section

namespace Yau.Proofs.Y01Aux

open Filter Yau.Blueprint Yau.Blueprint.Alignment

variable {n d N jBase j₀ : ℕ} {Q : ℕ → ℝ} {M hm Cd Dg : ℝ}

theorem polynomialModels_canonical_tail
    {X : KahlerManifold n} {o : Pt X} {ρ : STF X}
    {F : ℝ → ℝ → ComplexVector n → ComplexVector n} {tk : ℕ → ℝ}
    {H Hinv G Ginv : ℕ → PolyMap n}
    (hY07 : CanonicalGridTail) (hhm : 0 < hm) (hb : jBase ≤ j₀)
    (hbase : GridLayout Q N M hm jBase) (hnew : GridLayout Q N M hm j₀)
    (hρ : ∀ k, ρ o (tk k) = gridClock Q N M hm jBase k)
    (hmodels : PolynomialModels X o ρ F d hm Cd Dg tk H Hinv G Ginv) :
    let off := offset Q N M hm jBase j₀
    PolynomialModels X o ρ F d hm Cd Dg (fun k => tk (off + k))
      (fun k => H (off + k)) (fun k => Hinv (off + k))
      (fun k => G (off + k)) (fun k => Ginv (off + k)) := by
  let off := offset Q N M hm jBase j₀
  change PolynomialModels X o ρ F d hm Cd Dg (fun k => tk (off + k))
    (fun k => H (off + k)) (fun k => Hinv (off + k)) (fun k => G (off + k)) (fun k => Ginv (off + k))
  have htail := hY07 Q N M hm jBase j₀ hb hbase hnew
  have hsTail k : ρ o (tk (off + k)) = gridClock Q N M hm j₀ k :=
    (hρ (off + k)).trans (htail k).symm
  have hnat : Tendsto (fun k : ℕ => off + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat off
  rcases hmodels with ⟨hmono, hs, hmacro, hgap, hnorm, hjet, hdegree, hcoeff, hcenter, hforward⟩
  refine ⟨?_, hs.comp hnat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact hmono (Nat.add_lt_add_left hab off)
  · obtain ⟨c₁, C₁, hc₁, hzero, hendpoints, hsubdivision⟩ := canonical_macro_subdivision hhm hnew
    refine ⟨j₀, c₁, C₁, hc₁, ?_, ?_, ?_⟩
    · simpa only [hsTail, macroClock] using hzero
    · intro j hj
      obtain ⟨k, hk⟩ := hendpoints j hj
      exact ⟨k, by simpa only [hsTail, macroClock] using hk⟩
    · intro j hj
      simpa only [hsTail, macroClock] using hsubdivision j hj
  · obtain ⟨ch, hch, k₀, hgap⟩ := hgap
    refine ⟨ch, hch, k₀, ?_⟩
    intro k hk
    exact hgap (off + k) (by omega)
  · intro k
    exact hnorm (off + k)
  · intro k
    simpa only [Nat.add_assoc] using hjet (off + k)
  · intro k
    exact hdegree (off + k)
  · obtain ⟨η, hη, hbound⟩ := hcoeff
    refine ⟨(fun k => η (off + k)), hη.comp hnat, ?_⟩
    intro k
    simpa only [Nat.add_assoc] using hbound (off + k)
  · obtain ⟨Cp, hCp⟩ := hcenter
    refine ⟨Cp, ?_⟩
    intro k
    simpa only [Nat.add_assoc] using hCp (off + k)
  · apply all_forward_automorphisms
    intro k
    exact (hnorm (off + k)).2.2.2.2.1

end Yau.Proofs.Y01Aux
