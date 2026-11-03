import Yau.Proofs.F05BootstrapJetCommutation
import Yau.Proofs.F05BootstrapFiniteCalculus

/-! A finite commutator differentiates by the actual product rule. Its
Hessian factor uses the shorter solution word and its already regular
successor, through the proved rectangle identities. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_correction_calculus {ν d : Option (RIdx n)} {T α : ℝ}
    (hd : F05GoodLetter ν d) (s t : List (Option (RIdx n)))
    (a : Point n → Mat n) (b : Point n → RIdx n → ℝ) (u : Point n → ℝ)
    (ha : F05GoodDiffOn T d (F05GoodWord T s a) (F05PosPatch ν T))
    (hb : ∀ j, F05GoodDiffOn T d (F05GoodWord T s (fun z => b z j)) (F05PosPatch ν T))
    (hu : F05LocalSchauder α ν T (F05GoodWord T t u))
    (hdu : F05LocalSchauder α ν T (F05GoodWord T (d::t) u)) :
    F05GoodDiffOn T d (F05GoodCorrection T (F05PosSpace ν) a b u s t) (F05PosPatch ν T) ∧
      EqOn (F05GoodPartial T d (F05GoodCorrection T (F05PosSpace ν) a b u s t))
        (fun z => F05GoodCorrection T (F05PosSpace ν) a b u (d::s) t z+
          F05GoodCorrection T (F05PosSpace ν) a b u s (d::t) z) (F05PosPatch ν T) := by
  let X := F05PosSpace ν
  let Q := F05PosPatch ν T
  let v := F05GoodWord T t u
  let A := F05GoodWord T s a
  let B : RIdx n → Point n → ℝ := fun j => F05GoodWord T s (fun z => b z j)
  have hJets := F05_good_relative_jet_calculus hd hu hdu
  let LG (j : RIdx n) : (Space n →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (realVec j)
  let LH (j k : RIdx n) : (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (LG k).comp (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] ℝ) (realVec j))
  let P (j k : RIdx n) (z : Point n) := A z j k*F05RelDD X v z (realVec j) (realVec k)
  let R (j : RIdx n) (z : Point n) := B j z*F05RelD X v z (realVec j)
  have hAE (j k : RIdx n) : F05GoodDiffOn T d (fun z => A z j k) Q :=
    F05_good_diff_clm (matrixEntryCLM j k) ha
  have hH (j k : RIdx n) : F05GoodDiffOn T d (fun z => F05RelDD X v z (realVec j) (realVec k)) Q :=
    F05_good_diff_clm (LH j k) hJets.2.1
  have hG (j : RIdx n) : F05GoodDiffOn T d (fun z => F05RelD X v z (realVec j)) Q :=
    F05_good_diff_clm (LG j) hJets.1.1
  have hP (j k : RIdx n) : F05GoodDiffOn T d (P j k) Q := F05_good_diff_mul (hAE j k) (hH j k)
  have hR (j : RIdx n) : F05GoodDiffOn T d (R j) Q := F05_good_diff_mul (hb j) (hG j)
  have hRows (j : RIdx n) := F05_good_diff_finset_sum Finset.univ (fun k _ => hP j k)
  have hPrincipal := F05_good_diff_finset_sum Finset.univ (fun j _ => hRows j)
  have hDrift := F05_good_diff_finset_sum Finset.univ (fun j _ => hR j)
  refine ⟨F05_good_diff_add hPrincipal hDrift,?_⟩
  intro z hz
  have hAEq (j k : RIdx n) : F05GoodPartial T d (fun p => A p j k) z =
      F05GoodWord T (d::s) a z j k := by
    exact F05_good_partial_clm (matrixEntryCLM j k) ha hz hz.2
  have hHEq (j k : RIdx n) :
      F05GoodPartial T d (fun p => F05RelDD X v p (realVec j) (realVec k)) z =
        F05RelDD X (F05GoodWord T (d::t) u) z (realVec j) (realVec k) := by
    change F05GoodPartial T d (fun p => LH j k (F05RelDD X v p)) z = _
    rw [F05_good_partial_clm (LH j k) hJets.2.1 hz hz.2,hJets.2.2 hz]
    rfl
  have hGEq (j : RIdx n) :
      F05GoodPartial T d (fun p => F05RelD X v p (realVec j)) z =
        F05RelD X (F05GoodWord T (d::t) u) z (realVec j) := by
    change F05GoodPartial T d (fun p => LG j (F05RelD X v p)) z = _
    rw [F05_good_partial_clm (LG j) hJets.1.1 hz hz.2,hJets.1.2 hz]
    rfl
  have hPEq (j k : RIdx n) : F05GoodPartial T d (P j k) z =
      F05GoodWord T (d::s) a z j k*F05RelDD X v z (realVec j) (realVec k)+
        A z j k*F05RelDD X (F05GoodWord T (d::t) u) z (realVec j) (realVec k) := by
    change F05GoodPartial T d (fun p => A p j k*F05RelDD X v p (realVec j) (realVec k)) z = _
    rw [F05_good_partial_mul (hAE j k) (hH j k) hz,hAEq j k,hHEq j k]
  have hREq (j : RIdx n) : F05GoodPartial T d (R j) z =
      F05GoodWord T (d::s) (fun p => b p j) z*F05RelD X v z (realVec j)+
        B j z*F05RelD X (F05GoodWord T (d::t) u) z (realVec j) := by
    change F05GoodPartial T d (fun p => B j p*F05RelD X v p (realVec j)) z = _
    rw [F05_good_partial_mul (hb j) (hG j) hz,hGEq j]
    rfl
  have hPSum : F05GoodPartial T d (fun p => ∑ j,∑ k,P j k p) z =
      ∑ j,∑ k,(F05GoodWord T (d::s) a z j k*F05RelDD X v z (realVec j) (realVec k)+
        A z j k*F05RelDD X (F05GoodWord T (d::t) u) z (realVec j) (realVec k)) := by
    rw [F05_good_partial_finset_sum Finset.univ (fun j _ => hRows j) hz]
    apply Finset.sum_congr rfl
    intro j hj
    rw [F05_good_partial_finset_sum Finset.univ (fun k _ => hP j k) hz]
    exact Finset.sum_congr rfl (fun k hk => hPEq j k)
  have hRSum : F05GoodPartial T d (fun p => ∑ j,R j p) z =
      ∑ j,(F05GoodWord T (d::s) (fun p => b p j) z*F05RelD X v z (realVec j)+
        B j z*F05RelD X (F05GoodWord T (d::t) u) z (realVec j)) := by
    rw [F05_good_partial_finset_sum Finset.univ (fun j _ => hR j) hz]
    exact Finset.sum_congr rfl (fun j hj => hREq j)
  change F05GoodPartial T d (fun p => (∑ j,∑ k,P j k p)+∑ j,R j p) z = _
  rw [F05_good_partial_add hPrincipal hDrift hz,hPSum,hRSum]
  simp only [F05GoodCorrection,Finset.sum_add_distrib]
  ring

end Yau.Proofs.F05Aux
