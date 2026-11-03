import Yau.Proofs.Y02JetSubstitution
import Yau.Proofs.Y02JacobianComposition

/-! A finite list of shears corrects a homogeneous jet and carries an actual inverse. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ} {ι : Type*}

theorem shear_eq_id_add (l v : Fin n → ℂ) (m : ℕ) (c : ℂ) :
    shear l v m c = PolyMap.id + c • shearField l v m := by
  funext i
  simp only [shear, PolyMap.id, Pi.add_apply, Pi.smul_apply, shearField, smul_eq_C_mul, map_mul]
  ring

theorem shear_tangentId (l v : Fin n → ℂ) {m : ℕ} (hm : 2 ≤ m) (c : ℂ) :
    tangentId (shear l v m c) :=
  (tangentId_iff_jetEq _).mpr (shear_jetEq_id l v m 1 c (by omega))

theorem degree_id_le_one : (PolyMap.id : PolyMap n).degree ≤ 1 := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  simp [PolyMap.id]

def shearFoldForward (l v : ι → Fin n → ℂ) (m : ℕ) (c : ι → ℂ) :
    List ι → PolyMap n → PolyMap n
  | [], G => G
  | t :: L, G => shearFoldForward l v m c L ((shear (l t) (v t) m (c t)).comp G)

def shearFoldInverse (l v : ι → Fin n → ℂ) (m : ℕ) (c : ι → ℂ) :
    List ι → PolyMap n → PolyMap n
  | [], Ginv => Ginv
  | t :: L, Ginv => shearFoldInverse l v m c L (Ginv.comp (shear (l t) (v t) m (-c t)))

theorem shearFold_properties (l v : ι → Fin n → ℂ) {m : ℕ} (hm : 2 ≤ m)
    (c : ι → ℂ) (horth : ∀ t, ∑ i, l t i * v t i = 0) (L : List ι)
    (G Ginv : PolyMap n) (hpair : IsPolyAutomorphism G Ginv)
    (hG : tangentId G) (hGinv : tangentId Ginv) (hdet : G.jacDet = 1) (hdetinv : Ginv.jacDet = 1) :
    IsPolyAutomorphism (shearFoldForward l v m c L G) (shearFoldInverse l v m c L Ginv) ∧
      tangentId (shearFoldForward l v m c L G) ∧
      tangentId (shearFoldInverse l v m c L Ginv) ∧
      (shearFoldForward l v m c L G).jacDet = 1 ∧
      (shearFoldInverse l v m c L Ginv).jacDet = 1 ∧
      PolyMap.JetEq (shearFoldForward l v m c L G)
        (G + (L.map (fun t => c t • shearField (l t) (v t) m)).sum) m := by
  induction L generalizing G Ginv with
  | nil => simpa [shearFoldForward, shearFoldInverse] using
      And.intro hpair (And.intro hG (And.intro hGinv (And.intro hdet (And.intro hdetinv (jetEq_refl G m)))))
  | cons t L ih =>
    let S := shear (l t) (v t) m (c t)
    let T := shear (l t) (v t) m (-c t)
    have hST : IsPolyAutomorphism S T := shear_automorphism (l t) (v t) m (c t) (horth t)
    have hnew := automorphism_comp hST hpair
    have hS : tangentId S := shear_tangentId (l t) (v t) hm (c t)
    have hT : tangentId T := shear_tangentId (l t) (v t) hm (-c t)
    have hdetnew : (S.comp G).jacDet = 1 := by
      rw [jacDet_comp, shear_jacDet (l t) (v t) m (c t) (horth t), hdet]
      simp
    have hdetinvnew : (Ginv.comp T).jacDet = 1 := by
      rw [jacDet_comp, hdetinv, shear_jacDet (l t) (v t) m (-c t) (horth t)]
      simp
    obtain ⟨hpairF, hGF, hGinvF, hdetF, hdetinvF, hjetF⟩ :=
      ih (S.comp G) (Ginv.comp T) hnew (tangentId_comp hS hG) (tangentId_comp hGinv hT)
        hdetnew hdetinvnew
    refine ⟨hpairF, hGF, hGinvF, hdetF, hdetinvF, ?_⟩
    have hH : c t • shearField (l t) (v t) m ∈ homogeneousFields n m :=
      (homogeneousFields n m).smul_mem (c t) (shearField_homogeneous (l t) (v t) m)
    have hstep : PolyMap.JetEq (S.comp G) (G + c t • shearField (l t) (v t) m) m := by
      rw [show S = PolyMap.id + c t • shearField (l t) (v t) m from shear_eq_id_add _ _ _ _]
      exact homogeneous_perturbation_comp G _ hG hH
    have hjet := jetEq_trans hjetF (jetEq_add hstep
      (jetEq_refl (L.map (fun t => c t • shearField (l t) (v t) m)).sum m))
    simpa only [shearFoldForward, List.map_cons, List.sum_cons, add_assoc] using hjet

theorem finite_shears_jet {m N : ℕ} (hm : 2 ≤ m)
    (l v : Fin N → Fin n → ℂ) (c : Fin N → ℂ)
    (horth : ∀ t, ∑ i, l t i * v t i = 0) :
    ∃ F Finv : PolyMap n, IsPolyAutomorphism F Finv ∧ tangentId F ∧ tangentId Finv ∧
      F.jacDet = 1 ∧ Finv.jacDet = 1 ∧
      PolyMap.JetEq F (PolyMap.id + ∑ t, c t • shearField (l t) (v t) m) m := by
  refine ⟨shearFoldForward l v m c (List.finRange N) PolyMap.id,
    shearFoldInverse l v m c (List.finRange N) PolyMap.id, ?_⟩
  have h := shearFold_properties l v hm c horth (List.finRange N) PolyMap.id PolyMap.id
    automorphism_id tangentId_id tangentId_id jacDet_id jacDet_id
  simpa only [← List.ofFn_eq_map, List.sum_ofFn] using h

end Yau.Proofs.Y02Aux
