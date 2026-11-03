import spec.STATEMENT

-- The endpoints have exactly these types (definitions in `Yau/Geometry/Basic.lean`).
example {n : ℕ} (hn : 1 ≤ n) (X : Yau.KahlerManifold n) :
    Yau.BiholomorphicToComplexEuclidean X.manifold :=
  Yau.main hn X
example : Nonempty (Yau.KahlerManifold 1) :=
  Yau.main_nonvacuous

#print axioms Yau.main
#print axioms Yau.main_nonvacuous
