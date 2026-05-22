import Mathlib

noncomputable section

def f : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 3 + MvPolynomial.X 2 ^ 7

abbrev A := MvPolynomial (Fin 3) ℂ ⧸ Ideal.span {f}

instance : IsDomain A := by sorry

instance : UniqueFactorizationMonoid A := by sorry

end
